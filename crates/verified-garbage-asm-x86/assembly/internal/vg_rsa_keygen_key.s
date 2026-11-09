// The functions of `src/internal/vg_rsa_keygen_key.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_keygen_key:
	push ebx
	push ebp
	push esi
	push edi
	mov edi, DWORD PTR [esp+84]
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+68], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov ecx, 0
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	mov eax, 0
20:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 20b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
21:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 21b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov eax, 1
	mov DWORD PTR [ebp], eax
	mov esi, DWORD PTR [esp+36]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov ecx, DWORD PTR [esp+40]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 4
	shr ecx, 2
22:
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [ebx], eax
	add esi, 4
	sub ebx, 4
	sub ecx, 1
	jne 22b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
23:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 23b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+40]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
24:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 24b
	mov edi, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov ecx, DWORD PTR [esp+40]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 4
	shr ecx, 2
25:
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [ebx], eax
	add esi, 4
	sub ebx, 4
	sub ecx, 1
	jne 25b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
26:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 26b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+40]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
27:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 27b
	mov edi, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+76]
	mov ecx, DWORD PTR [esp+80]
	mov eax, 0
	mov ebp, edi
28:
	mov DWORD PTR [ebp+80], eax
	add ebp, 4
	mov edx, edi
	add edx, 8
	cmp ebp, edx
	jne 28b
	mov ebx, edi
	add ebx, 80
	add esi, ecx
	sub esi, 1
29:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 29b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
210:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 210b
	mov ebp, edi
	add ebp, 80
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+80]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
211:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 211b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
212:
	cmp edx, 32
	jae 213f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 214f
213:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
214:
	cmp edx, 0
	jne 212b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+92], ebx
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 215f
	jmp 216f
215:
217:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 217b
216:
	and edi, 15
	jne 218f
	jmp 219f
218:
220:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 220b
219:
	mov edi, DWORD PTR [esp+84]
	mov ecx, 0
	sub ecx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 221f
	jmp 222f
221:
223:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 223b
222:
	and edi, 15
	jne 224f
	jmp 225f
224:
226:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 226b
225:
	mov edi, DWORD PTR [esp+84]
	mov ecx, 0
	sub ecx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 227f
	jmp 228f
227:
229:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 229b
228:
	and edi, 15
	jne 230f
	jmp 231f
230:
232:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 232b
231:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
233:
	cmp edx, 32
	jae 234f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 235f
234:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
235:
	cmp edx, 0
	jne 233b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
236:
	cmp edx, 32
	jae 237f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 238f
237:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
238:
	cmp edx, 0
	jne 236b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+92], ebx
	mov ecx, 0
	sub ecx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 239f
	jmp 240f
239:
241:
	movdqu xmm0, XMMWORD PTR [ebp]
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi], xmm0
	add ebp, 16
	add ebx, 16
	add edi, 16
	sub eax, 1
	jne 241b
240:
	and edx, 15
	jne 242f
	jmp 243f
242:
244:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 244b
243:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
245:
	cmp edx, 32
	jae 246f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 247f
246:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
247:
	cmp edx, 0
	jne 245b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
248:
	cmp edx, 32
	jae 249f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 250f
249:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
250:
	cmp edx, 0
	jne 248b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
251:
	cmp edx, 32
	jae 252f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 253f
252:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
253:
	cmp edx, 0
	jne 251b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+92], ebx
	mov ecx, 0
	sub ecx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 254f
	jmp 255f
254:
256:
	movdqu xmm0, XMMWORD PTR [ebp]
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi], xmm0
	add ebp, 16
	add ebx, 16
	add edi, 16
	sub eax, 1
	jne 256b
255:
	and edx, 15
	jne 257f
	jmp 258f
257:
259:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 259b
258:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
260:
	cmp edx, 32
	jae 261f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 262f
261:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
262:
	cmp edx, 0
	jne 260b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+40]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, DWORD PTR [esp+40]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add ecx, eax
	add ecx, 8
	mov eax, 0
263:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 263b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
264:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, ebp
	sub ecx, eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, ecx
	mov edx, DWORD PTR [eax]
	mov DWORD PTR [edi+128], edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ecx, edi
	add ecx, 160
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	mov esi, DWORD PTR [esp+40]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	mov ebx, 0
265:
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [ecx]
	mul edx
	add eax, DWORD PTR [ebp]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add ecx, 4
	add ebp, 4
	sub esi, 4
	jne 265b
	mov DWORD PTR [ebp], ebx
	mov eax, DWORD PTR [esp+40]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	sub ebp, eax
	add ebp, 4
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	cmp ebp, eax
	jne 264b
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 266f
	jmp 267f
266:
268:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 268b
267:
	and edi, 15
	jne 269f
	jmp 270f
269:
271:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 271b
270:
	mov edi, DWORD PTR [esp+84]
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 272f
	jmp 273f
272:
274:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 274b
273:
	and edi, 15
	jne 275f
	jmp 276f
275:
277:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 277b
276:
	mov edi, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+32]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
278:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, DWORD PTR [eax]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	or ecx, DWORD PTR [eax]
	and ecx, 1
	xor ecx, 1
	mov DWORD PTR [edi+92], ecx
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 279f
	jmp 280f
279:
281:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 281b
280:
	and edi, 15
	jne 282f
	jmp 283f
282:
284:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 284b
283:
	mov edi, DWORD PTR [esp+84]
	mov ebx, 0
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
285:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 285b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov ecx, 0
	sub ecx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 286f
	jmp 287f
286:
288:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 288b
287:
	and edi, 15
	jne 289f
	jmp 290f
289:
291:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 291b
290:
	mov edi, DWORD PTR [esp+84]
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 292f
	jmp 293f
292:
294:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 294b
293:
	and edi, 15
	jne 295f
	jmp 296f
295:
297:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 297b
296:
	mov edi, DWORD PTR [esp+84]
	mov ebx, 0
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
298:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 298b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov ecx, 0
	sub ecx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 299f
	jmp 2100f
299:
2101:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2101b
2100:
	and edi, 15
	jne 2102f
	jmp 2103f
2102:
2104:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2104b
2103:
	mov edi, DWORD PTR [esp+84]
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2105f
	jmp 2106f
2105:
2107:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2107b
2106:
	and edi, 15
	jne 2108f
	jmp 2109f
2108:
2110:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2110b
2109:
	mov edi, DWORD PTR [esp+84]
	mov ebx, 0
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
2111:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2111b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov ecx, 0
	sub ecx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2112f
	jmp 2113f
2112:
2114:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2114b
2113:
	and edi, 15
	jne 2115f
	jmp 2116f
2115:
2117:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2117b
2116:
	mov edi, DWORD PTR [esp+84]
	sub esi, 1
	cmp esi, 0
	jne 278b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+92]
	xor eax, 1
	mov DWORD PTR [edi+92], eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2118f
	jmp 2119f
2118:
2120:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2120b
2119:
	and edi, 15
	jne 2121f
	jmp 2122f
2121:
2123:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2123b
2122:
	mov edi, DWORD PTR [esp+84]
	mov ecx, 0
	sub ecx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2124f
	jmp 2125f
2124:
2126:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2126b
2125:
	and edi, 15
	jne 2127f
	jmp 2128f
2127:
2129:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2129b
2128:
	mov edi, DWORD PTR [esp+84]
	mov ecx, 0
	sub ecx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2130f
	jmp 2131f
2130:
2132:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2132b
2131:
	and edi, 15
	jne 2133f
	jmp 2134f
2133:
2135:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2135b
2134:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
2136:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2136b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov eax, 3
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2137:
	cmp edx, 32
	jae 2138f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2139f
2138:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2139:
	cmp edx, 0
	jne 2137b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov eax, 1
	sub eax, ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	and eax, DWORD PTR [ebp]
	and eax, 1
	mov DWORD PTR [edi+92], eax
	mov ecx, 0
	sub ecx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2140f
	jmp 2141f
2140:
2142:
	movdqu xmm0, XMMWORD PTR [ebp]
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi], xmm0
	add ebp, 16
	add ebx, 16
	add edi, 16
	sub eax, 1
	jne 2142b
2141:
	and edx, 15
	jne 2143f
	jmp 2144f
2143:
2145:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2145b
2144:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov ecx, 0
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	mov eax, 0
2146:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2146b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edi, DWORD PTR [esp+40]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2147:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2147b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+40]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2148:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2148b
	mov edi, DWORD PTR [esp+84]
	mov ecx, -1
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edi, DWORD PTR [esp+40]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2149f
	jmp 2150f
2149:
2151:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2151b
2150:
	and edi, 15
	jne 2152f
	jmp 2153f
2152:
2154:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2154b
2153:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2155:
	cmp edx, 32
	jae 2156f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2157f
2156:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2157:
	cmp edx, 0
	jne 2155b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov eax, DWORD PTR [esp+40]
	mov ecx, eax
	add ecx, 7
	shr ecx, 3
	mov edx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	sub ecx, edx
	add ecx, 35
	push eax
	push ecx
	push edi
	call {vg_rsa_keygen_inverse}
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
2158:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2158b
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+40]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2159:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2159b
	mov edi, DWORD PTR [esp+84]
	mov ecx, DWORD PTR [edi+92]
	sub ecx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2160f
	jmp 2161f
2160:
2162:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2162b
2161:
	and edi, 15
	jne 2163f
	jmp 2164f
2163:
2165:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2165b
2164:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2166:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2166b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2167:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2167b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2168:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2168b
	mov esi, DWORD PTR [esp+32]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2169:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2170:
	cmp edx, 32
	jae 2171f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2172f
2171:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2172:
	cmp edx, 0
	jne 2170b
	mov edi, DWORD PTR [esp+84]
	mov eax, ecx
	and eax, 1
	mov DWORD PTR [edi+136], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2173:
	cmp edx, 32
	jae 2174f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2175f
2174:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2175:
	cmp edx, 0
	jne 2173b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+136]
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2176:
	cmp edx, 32
	jae 2177f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2178f
2177:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2178:
	cmp edx, 0
	jne 2176b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	xor ebx, -1
	and ebx, 1
	xor ecx, -1
	mov DWORD PTR [edi+140], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2179f
	jmp 2180f
2179:
2181:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2181b
2180:
	and edi, 15
	jne 2182f
	jmp 2183f
2182:
2184:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2184b
2183:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+140]
	mov DWORD PTR [eax], ecx
	sub esi, 1
	cmp esi, 0
	jne 2169b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2185:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2185b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2186:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2186b
	mov edi, DWORD PTR [esp+84]
	mov eax, DWORD PTR [edi+80]
	xor eax, 0
	or eax, DWORD PTR [edi+84]
	cmp eax, 0
	je 2187f
	mov eax, DWORD PTR [edi+80]
	xor eax, 1
	or eax, DWORD PTR [edi+84]
	cmp eax, 0
	je 2189f
	mov eax, DWORD PTR [edi+80]
	and eax, 1
	cmp eax, 0
	je 2191f
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2193:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2193b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2194:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2194b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2195:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2195b
	mov esi, DWORD PTR [esp+32]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2196:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2197:
	cmp edx, 32
	jae 2198f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2199f
2198:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2199:
	cmp edx, 0
	jne 2197b
	mov edi, DWORD PTR [esp+84]
	mov eax, ecx
	and eax, 1
	mov DWORD PTR [edi+136], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2200:
	cmp edx, 32
	jae 2201f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2202f
2201:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2202:
	cmp edx, 0
	jne 2200b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+136]
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2203:
	cmp edx, 32
	jae 2204f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2205f
2204:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2205:
	cmp edx, 0
	jne 2203b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	xor ebx, -1
	and ebx, 1
	xor ecx, -1
	mov DWORD PTR [edi+140], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2206f
	jmp 2207f
2206:
2208:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2208b
2207:
	and edi, 15
	jne 2209f
	jmp 2210f
2209:
2211:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2211b
2210:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+140]
	mov DWORD PTR [eax], ecx
	sub esi, 1
	cmp esi, 0
	jne 2196b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2212:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2212b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2213:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2213b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov ecx, 0
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	mov eax, 0
2214:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2214b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edi, DWORD PTR [esp+80]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2215:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2215b
	mov edi, DWORD PTR [esp+84]
	mov ebp, edi
	add ebp, 80
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+80]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2216:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2216b
	mov edi, DWORD PTR [esp+84]
	mov ecx, -1
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edi, DWORD PTR [esp+80]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2217f
	jmp 2218f
2217:
2219:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2219b
2218:
	and edi, 15
	jne 2220f
	jmp 2221f
2220:
2222:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2222b
2221:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2223:
	cmp edx, 32
	jae 2224f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2225f
2224:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2225:
	cmp edx, 0
	jne 2223b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov eax, DWORD PTR [esp+80]
	mov ecx, eax
	add ecx, 7
	shr ecx, 3
	mov edx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	sub ecx, edx
	add ecx, 35
	push eax
	push ecx
	push edi
	call {vg_rsa_keygen_inverse}
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+80]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
2226:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2226b
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov eax, 1
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2227:
	cmp edx, 32
	jae 2228f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2229f
2228:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2229:
	cmp edx, 0
	jne 2227b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2230:
	cmp edx, 32
	jae 2231f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2232f
2231:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2232:
	cmp edx, 0
	jne 2230b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+92], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
2233:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2233b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov eax, 2
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2234:
	cmp edx, 32
	jae 2235f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2236f
2235:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2236:
	cmp edx, 0
	jne 2234b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov eax, 1
	sub eax, ebx
	and eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+88], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
2237:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2237b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+84]
	sub eax, DWORD PTR [edi+208]
	sbb edx, DWORD PTR [edi+212]
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], edx
	mov ebp, edi
	add ebp, 184
	mov ecx, DWORD PTR [esp+80]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, DWORD PTR [esp+80]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add ecx, eax
	add ecx, 8
	mov eax, 0
2238:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2238b
	mov ebp, edi
	add ebp, 184
2239:
	mov eax, edi
	add eax, 184
	mov ecx, ebp
	sub ecx, eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, ecx
	mov edx, DWORD PTR [eax]
	mov DWORD PTR [edi+128], edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ecx, edi
	add ecx, 160
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	mov esi, DWORD PTR [esp+80]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	mov ebx, 0
2240:
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [ecx]
	mul edx
	add eax, DWORD PTR [ebp]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add ecx, 4
	add ebp, 4
	sub esi, 4
	jne 2240b
	mov DWORD PTR [ebp], ebx
	mov eax, DWORD PTR [esp+80]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	sub ebp, eax
	add ebp, 4
	mov eax, edi
	add eax, 184
	mov edx, DWORD PTR [esp+80]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	cmp ebp, eax
	jne 2239b
	mov ebp, edi
	add ebp, 208
	mov ecx, 16
	add ecx, 8
	mov eax, 0
2241:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2241b
	mov ebp, edi
	add ebp, 208
	mov eax, 1
	mov DWORD PTR [ebp], eax
	mov ecx, 0
	mov ebp, edi
2242:
	mov eax, DWORD PTR [ebp+184]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+208]
	mov DWORD PTR [ebp+160], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 16
	cmp ebp, edx
	jne 2242b
	mov ebp, edi
	add ebp, 208
	mov ecx, 16
	add ecx, 8
	mov eax, 0
2243:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2243b
	mov ebp, edi
	add ebp, 80
	mov ebx, edi
	add ebx, 208
	mov edi, DWORD PTR [esp+80]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2244:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2244b
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov ebp, edi
2245:
	mov DWORD PTR [ebp+184], eax
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2245b
	mov esi, 128
2246:
	mov ecx, 0
	mov ebp, edi
2247:
	mov eax, DWORD PTR [ebp+160]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+232], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 16
	cmp ebp, edx
	jne 2247b
	mov ebx, ecx
	and ebx, 1
	mov ecx, 0
	mov ebp, edi
2248:
	mov eax, DWORD PTR [ebp+232]
	mov edx, DWORD PTR [ebp+232]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+160], eax
	add ebp, 4
	mov edx, edi
	add edx, 16
	cmp ebp, edx
	jne 2248b
	mov ecx, 0
	mov ebp, edi
2249:
	mov eax, DWORD PTR [ebp+184]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+184]
	mov DWORD PTR [ebp+232], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2249b
	mov ecx, 0
	mov ebp, edi
2250:
	mov eax, DWORD PTR [ebp+232]
	mov edx, DWORD PTR [ebp+232]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+184], eax
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2250b
	mov eax, DWORD PTR [edi+184]
	add eax, ebx
	mov DWORD PTR [edi+184], eax
	mov ecx, 0
	mov ebp, edi
2251:
	mov eax, DWORD PTR [ebp+184]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+208]
	mov DWORD PTR [ebp+232], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2251b
	mov ebx, ecx
	xor ebx, -1
	and ebx, 1
	xor ecx, -1
	mov ebp, edi
2252:
	mov eax, DWORD PTR [ebp+184]
	mov edx, DWORD PTR [ebp+232]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+184], eax
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2252b
	mov eax, DWORD PTR [edi+160]
	add eax, ebx
	mov DWORD PTR [edi+160], eax
	sub esi, 1
	cmp esi, 0
	jne 2246b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
2253:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2253b
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+80]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2254:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2254b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, DWORD PTR [esp+80]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add ecx, eax
	add ecx, 8
	mov eax, 0
2255:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2255b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
2256:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	mov ecx, ebp
	sub ecx, eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, ecx
	mov edx, DWORD PTR [eax]
	mov DWORD PTR [edi+128], edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ecx, edi
	add ecx, 160
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	mov esi, DWORD PTR [esp+80]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	mov ebx, 0
2257:
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [ecx]
	mul edx
	add eax, DWORD PTR [ebp]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add ecx, 4
	add ebp, 4
	sub esi, 4
	jne 2257b
	mov DWORD PTR [ebp], ebx
	mov eax, DWORD PTR [esp+80]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	sub ebp, eax
	add ebp, 4
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	cmp ebp, eax
	jne 2256b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2258:
	cmp edx, 32
	jae 2259f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2260f
2259:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2260:
	cmp edx, 0
	jne 2258b
	mov edi, DWORD PTR [esp+84]
	jmp 2192f
2191:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
2261:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2261b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov eax, 3
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2262:
	cmp edx, 32
	jae 2263f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2264f
2263:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2264:
	cmp edx, 0
	jne 2262b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov eax, 1
	sub eax, ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	and eax, DWORD PTR [ebp]
	and eax, 1
	mov DWORD PTR [edi+92], eax
	mov ecx, 0
	sub ecx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2265f
	jmp 2266f
2265:
2267:
	movdqu xmm0, XMMWORD PTR [ebp]
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi], xmm0
	add ebp, 16
	add ebx, 16
	add edi, 16
	sub eax, 1
	jne 2267b
2266:
	and edx, 15
	jne 2268f
	jmp 2269f
2268:
2270:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2270b
2269:
	mov edi, DWORD PTR [esp+84]
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+88], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2271:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2271b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2272:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2272b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2273:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2273b
	mov esi, DWORD PTR [esp+32]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2274:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2275:
	cmp edx, 32
	jae 2276f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2277f
2276:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2277:
	cmp edx, 0
	jne 2275b
	mov edi, DWORD PTR [esp+84]
	mov eax, ecx
	and eax, 1
	mov DWORD PTR [edi+136], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2278:
	cmp edx, 32
	jae 2279f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2280f
2279:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2280:
	cmp edx, 0
	jne 2278b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+136]
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2281:
	cmp edx, 32
	jae 2282f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2283f
2282:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2283:
	cmp edx, 0
	jne 2281b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	xor ebx, -1
	and ebx, 1
	xor ecx, -1
	mov DWORD PTR [edi+140], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2284f
	jmp 2285f
2284:
2286:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2286b
2285:
	and edi, 15
	jne 2287f
	jmp 2288f
2287:
2289:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2289b
2288:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+140]
	mov DWORD PTR [eax], ecx
	sub esi, 1
	cmp esi, 0
	jne 2274b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2290:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2290b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2291:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2291b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov ecx, 0
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	mov eax, 0
2292:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2292b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2293:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2293b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2294:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2294b
	mov edi, DWORD PTR [esp+84]
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2295f
	jmp 2296f
2295:
2297:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2297b
2296:
	and edi, 15
	jne 2298f
	jmp 2299f
2298:
2300:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2300b
2299:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2301:
	cmp edx, 32
	jae 2302f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2303f
2302:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2303:
	cmp edx, 0
	jne 2301b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov eax, DWORD PTR [esp+32]
	mov ecx, eax
	add ecx, 7
	shr ecx, 3
	mov edx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	sub ecx, edx
	add ecx, 35
	push eax
	push ecx
	push edi
	call {vg_rsa_keygen_inverse}
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
2304:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2304b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov eax, 1
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2305:
	cmp edx, 32
	jae 2306f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2307f
2306:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2307:
	cmp edx, 0
	jne 2305b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2308:
	cmp edx, 32
	jae 2309f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2310f
2309:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2310:
	cmp edx, 0
	jne 2308b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+92], ebx
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+88], eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2311f
	jmp 2312f
2311:
2313:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2313b
2312:
	and edi, 15
	jne 2314f
	jmp 2315f
2314:
2316:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2316b
2315:
	mov edi, DWORD PTR [esp+84]
2192:
	jmp 2190f
2189:
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2317f
	jmp 2318f
2317:
2319:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2319b
2318:
	and edi, 15
	jne 2320f
	jmp 2321f
2320:
2322:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2322b
2321:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2323:
	cmp edx, 32
	jae 2324f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2325f
2324:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2325:
	cmp edx, 0
	jne 2323b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2326:
	cmp edx, 32
	jae 2327f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2328f
2327:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2328:
	cmp edx, 0
	jne 2326b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+92], ebx
	mov eax, 1
	sub eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+88], eax
2190:
	jmp 2188f
2187:
	mov eax, 0
	mov DWORD PTR [edi+88], eax
2188:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
2329:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2329b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov eax, 1
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov eax, 1
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2330:
	cmp edx, 32
	jae 2331f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2332f
2331:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2332:
	cmp edx, 0
	jne 2330b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov eax, DWORD PTR [edi+88]
	and eax, ebx
	cmp eax, 0
	jne 2333f
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
2335:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2335b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov eax, 3
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2336:
	cmp edx, 32
	jae 2337f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2338f
2337:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2338:
	cmp edx, 0
	jne 2336b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov eax, 1
	sub eax, ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	and eax, DWORD PTR [ebp]
	and eax, 1
	mov DWORD PTR [edi+92], eax
	mov ecx, 0
	sub ecx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2339f
	jmp 2340f
2339:
2341:
	movdqu xmm0, XMMWORD PTR [ebp]
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi], xmm0
	add ebp, 16
	add ebx, 16
	add edi, 16
	sub eax, 1
	jne 2341b
2340:
	and edx, 15
	jne 2342f
	jmp 2343f
2342:
2344:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2344b
2343:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov ecx, 0
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	mov eax, 0
2345:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2345b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edi, DWORD PTR [esp+40]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2346:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2346b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+40]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2347:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2347b
	mov edi, DWORD PTR [esp+84]
	mov ecx, -1
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edi, DWORD PTR [esp+40]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2348f
	jmp 2349f
2348:
2350:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2350b
2349:
	and edi, 15
	jne 2351f
	jmp 2352f
2351:
2353:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2353b
2352:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2354:
	cmp edx, 32
	jae 2355f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2356f
2355:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2356:
	cmp edx, 0
	jne 2354b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov eax, DWORD PTR [esp+40]
	mov ecx, eax
	add ecx, 7
	shr ecx, 3
	mov edx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	sub ecx, edx
	add ecx, 35
	push eax
	push ecx
	push edi
	call {vg_rsa_keygen_inverse}
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+40]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
2357:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2357b
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov eax, 1
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2358:
	cmp edx, 32
	jae 2359f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2360f
2359:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2360:
	cmp edx, 0
	jne 2358b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2361:
	cmp edx, 32
	jae 2362f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2363f
2362:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2363:
	cmp edx, 0
	jne 2361b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+92], ebx
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+88], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
2364:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2364b
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+40]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2365:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2365b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
2366:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2366b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2367:
	cmp edx, 32
	jae 2368f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2369f
2368:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2369:
	cmp edx, 0
	jne 2367b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2370:
	cmp edx, 32
	jae 2371f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2372f
2371:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2372:
	cmp edx, 0
	jne 2370b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+92], ebx
	mov ecx, 0
	sub ecx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2373f
	jmp 2374f
2373:
2375:
	movdqu xmm0, XMMWORD PTR [ebp]
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi], xmm0
	add ebp, 16
	add ebx, 16
	add edi, 16
	sub eax, 1
	jne 2375b
2374:
	and edx, 15
	jne 2376f
	jmp 2377f
2376:
2378:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2378b
2377:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2379:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2379b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2380:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2380b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2381:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2381b
	mov esi, DWORD PTR [esp+32]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2382:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2383:
	cmp edx, 32
	jae 2384f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2385f
2384:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2385:
	cmp edx, 0
	jne 2383b
	mov edi, DWORD PTR [esp+84]
	mov eax, ecx
	and eax, 1
	mov DWORD PTR [edi+136], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2386:
	cmp edx, 32
	jae 2387f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2388f
2387:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2388:
	cmp edx, 0
	jne 2386b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+136]
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2389:
	cmp edx, 32
	jae 2390f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2391f
2390:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2391:
	cmp edx, 0
	jne 2389b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	xor ebx, -1
	and ebx, 1
	xor ecx, -1
	mov DWORD PTR [edi+140], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2392f
	jmp 2393f
2392:
2394:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2394b
2393:
	and edi, 15
	jne 2395f
	jmp 2396f
2395:
2397:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2397b
2396:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+140]
	mov DWORD PTR [eax], ecx
	sub esi, 1
	cmp esi, 0
	jne 2382b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2398:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2398b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2399:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2399b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
2400:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2400b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2401:
	cmp edx, 32
	jae 2402f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2403f
2402:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2403:
	cmp edx, 0
	jne 2401b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2404:
	cmp edx, 32
	jae 2405f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2406f
2405:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2406:
	cmp edx, 0
	jne 2404b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+92], ebx
	mov ecx, 0
	sub ecx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2407f
	jmp 2408f
2407:
2409:
	movdqu xmm0, XMMWORD PTR [ebp]
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi], xmm0
	add ebp, 16
	add ebx, 16
	add edi, 16
	sub eax, 1
	jne 2409b
2408:
	and edx, 15
	jne 2410f
	jmp 2411f
2410:
2412:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2412b
2411:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2413:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2413b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2414:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2414b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2415:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2415b
	mov esi, DWORD PTR [esp+32]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2416:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2417:
	cmp edx, 32
	jae 2418f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2419f
2418:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2419:
	cmp edx, 0
	jne 2417b
	mov edi, DWORD PTR [esp+84]
	mov eax, ecx
	and eax, 1
	mov DWORD PTR [edi+136], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2420:
	cmp edx, 32
	jae 2421f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2422f
2421:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2422:
	cmp edx, 0
	jne 2420b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+136]
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2423:
	cmp edx, 32
	jae 2424f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2425f
2424:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2425:
	cmp edx, 0
	jne 2423b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	xor ebx, -1
	and ebx, 1
	xor ecx, -1
	mov DWORD PTR [edi+140], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2426f
	jmp 2427f
2426:
2428:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2428b
2427:
	and edi, 15
	jne 2429f
	jmp 2430f
2429:
2431:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2431b
2430:
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+140]
	mov DWORD PTR [eax], ecx
	sub esi, 1
	cmp esi, 0
	jne 2416b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2432:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2432b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ecx, -1
2433:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2433b
	mov edi, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+40]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, DWORD PTR [esp+40]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add ecx, eax
	add ecx, 8
	mov eax, 0
2434:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2434b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
2435:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, ebp
	sub ecx, eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, ecx
	mov edx, DWORD PTR [eax]
	mov DWORD PTR [edi+128], edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ecx, edi
	add ecx, 160
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	mov esi, DWORD PTR [esp+40]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	mov ebx, 0
2436:
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [ecx]
	mul edx
	add eax, DWORD PTR [ebp]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add ecx, 4
	add ebp, 4
	sub esi, 4
	jne 2436b
	mov DWORD PTR [ebp], ebx
	mov eax, DWORD PTR [esp+40]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	sub ebp, eax
	add ebp, 4
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	cmp ebp, eax
	jne 2435b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	sub ebp, 4
	mov eax, DWORD PTR [ebp]
	shr eax, 31
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+88], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+88], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+88], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+84]
	cmp eax, 2
	sbb eax, eax
	and eax, 1
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+88], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
2437:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2437b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov eax, 3
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2438:
	cmp edx, 32
	jae 2439f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2440f
2439:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2440:
	cmp edx, 0
	jne 2438b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+92], eax
	mov eax, 1
	sub eax, ebx
	and eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+96], eax
	jmp 2334f
2333:
	mov eax, 0
	mov DWORD PTR [edi+88], eax
	mov eax, 2
	mov DWORD PTR [edi+96], eax
2334:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov eax, 0
2441:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2441b
	mov ecx, DWORD PTR [edi+88]
	sub ecx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2442f
	jmp 2443f
2442:
2444:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2444b
2443:
	and edi, 15
	jne 2445f
	jmp 2446f
2445:
2447:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2447b
2446:
	mov edi, DWORD PTR [esp+84]
	mov ebx, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, ecx
	sub esi, 1
2448:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2448b
	mov ecx, DWORD PTR [edi+88]
	sub ecx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2449f
	jmp 2450f
2449:
2451:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2451b
2450:
	and edi, 15
	jne 2452f
	jmp 2453f
2452:
2454:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2454b
2453:
	mov edi, DWORD PTR [esp+84]
	mov ebx, DWORD PTR [esp+28]
	mov ecx, DWORD PTR [esp+32]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, ecx
	sub esi, 1
2455:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2455b
	mov ecx, DWORD PTR [edi+88]
	sub ecx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2456f
	jmp 2457f
2456:
2458:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2458b
2457:
	and edi, 15
	jne 2459f
	jmp 2460f
2459:
2461:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2461b
2460:
	mov edi, DWORD PTR [esp+84]
	mov ebx, DWORD PTR [esp+36]
	mov ecx, DWORD PTR [esp+40]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, ecx
	sub esi, 1
2462:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2462b
	mov ecx, DWORD PTR [edi+88]
	sub ecx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2463f
	jmp 2464f
2463:
2465:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2465b
2464:
	and edi, 15
	jne 2466f
	jmp 2467f
2466:
2468:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2468b
2467:
	mov edi, DWORD PTR [esp+84]
	mov ebx, DWORD PTR [esp+44]
	mov ecx, DWORD PTR [esp+48]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, ecx
	sub esi, 1
2469:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2469b
	mov ecx, DWORD PTR [edi+88]
	sub ecx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2470f
	jmp 2471f
2470:
2472:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2472b
2471:
	and edi, 15
	jne 2473f
	jmp 2474f
2473:
2475:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2475b
2474:
	mov edi, DWORD PTR [esp+84]
	mov ebx, DWORD PTR [esp+52]
	mov ecx, DWORD PTR [esp+56]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, ecx
	sub esi, 1
2476:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2476b
	mov ecx, DWORD PTR [edi+88]
	sub ecx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2477f
	jmp 2478f
2477:
2479:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2479b
2478:
	and edi, 15
	jne 2480f
	jmp 2481f
2480:
2482:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2482b
2481:
	mov edi, DWORD PTR [esp+84]
	mov ebx, DWORD PTR [esp+60]
	mov ecx, DWORD PTR [esp+64]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, ecx
	sub esi, 1
2483:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2483b
	mov ecx, DWORD PTR [edi+88]
	sub ecx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2484f
	jmp 2485f
2484:
2486:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2486b
2485:
	and edi, 15
	jne 2487f
	jmp 2488f
2487:
2489:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2489b
2488:
	mov edi, DWORD PTR [esp+84]
	mov ebx, DWORD PTR [esp+68]
	mov ecx, DWORD PTR [esp+72]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, ecx
	sub esi, 1
2490:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2490b
	mov eax, DWORD PTR [edi+96]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
