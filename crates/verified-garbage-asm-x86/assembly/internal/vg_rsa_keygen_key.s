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
	call {vg_rsa_keygen_div}
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
2168:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2168b
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
2169:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2169b
	mov edi, DWORD PTR [esp+84]
	mov eax, DWORD PTR [edi+80]
	xor eax, 0
	or eax, DWORD PTR [edi+84]
	cmp eax, 0
	je 2170f
	mov eax, DWORD PTR [edi+80]
	xor eax, 1
	or eax, DWORD PTR [edi+84]
	cmp eax, 0
	je 2172f
	mov eax, DWORD PTR [edi+80]
	and eax, 1
	cmp eax, 0
	je 2174f
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
2176:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2176b
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
2177:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2177b
	mov edi, DWORD PTR [esp+84]
	call {vg_rsa_keygen_div}
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
2178:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2178b
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
2179:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2179b
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
2180:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2180b
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
2181:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2181b
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
2182:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2182b
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
	jne 2183f
	jmp 2184f
2183:
2185:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2185b
2184:
	and edi, 15
	jne 2186f
	jmp 2187f
2186:
2188:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2188b
2187:
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
2189:
	cmp edx, 32
	jae 2190f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2191f
2190:
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
2191:
	cmp edx, 0
	jne 2189b
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
2192:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2192b
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
2193:
	cmp edx, 32
	jae 2194f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2195f
2194:
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
2195:
	cmp edx, 0
	jne 2193b
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
2196:
	cmp edx, 32
	jae 2197f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2198f
2197:
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
2198:
	cmp edx, 0
	jne 2196b
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
2199:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2199b
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
2200:
	cmp edx, 32
	jae 2201f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
2202:
	cmp edx, 0
	jne 2200b
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
2203:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2203b
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
2204:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2204b
	mov ebp, edi
	add ebp, 184
2205:
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
2206:
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
	jne 2206b
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
	jne 2205b
	mov ebp, edi
	add ebp, 208
	mov ecx, 16
	add ecx, 8
	mov eax, 0
2207:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2207b
	mov ebp, edi
	add ebp, 208
	mov eax, 1
	mov DWORD PTR [ebp], eax
	mov ecx, 0
	mov ebp, edi
2208:
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
	jne 2208b
	mov ebp, edi
	add ebp, 208
	mov ecx, 16
	add ecx, 8
	mov eax, 0
2209:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2209b
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
2210:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2210b
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov ebp, edi
2211:
	mov DWORD PTR [ebp+184], eax
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2211b
	mov esi, 128
2212:
	mov ecx, 0
	mov ebp, edi
2213:
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
	jne 2213b
	mov ebx, ecx
	and ebx, 1
	mov ecx, 0
	mov ebp, edi
2214:
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
	jne 2214b
	mov ecx, 0
	mov ebp, edi
2215:
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
	jne 2215b
	mov ecx, 0
	mov ebp, edi
2216:
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
	jne 2216b
	mov eax, DWORD PTR [edi+184]
	add eax, ebx
	mov DWORD PTR [edi+184], eax
	mov ecx, 0
	mov ebp, edi
2217:
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
	jne 2217b
	mov ebx, ecx
	xor ebx, -1
	and ebx, 1
	xor ecx, -1
	mov ebp, edi
2218:
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
	jne 2218b
	mov eax, DWORD PTR [edi+160]
	add eax, ebx
	mov DWORD PTR [edi+160], eax
	sub esi, 1
	cmp esi, 0
	jne 2212b
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
2219:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2219b
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
2220:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2220b
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
2221:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2221b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
2222:
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
2223:
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
	jne 2223b
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
	jne 2222b
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
2224:
	cmp edx, 32
	jae 2225f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2226f
2225:
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
2226:
	cmp edx, 0
	jne 2224b
	mov edi, DWORD PTR [esp+84]
	jmp 2175f
2174:
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
2227:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2227b
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
2228:
	cmp edx, 32
	jae 2229f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2230f
2229:
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
2230:
	cmp edx, 0
	jne 2228b
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
	jne 2231f
	jmp 2232f
2231:
2233:
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
	jne 2233b
2232:
	and edx, 15
	jne 2234f
	jmp 2235f
2234:
2236:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2236b
2235:
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
2237:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2237b
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
2238:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2238b
	mov edi, DWORD PTR [esp+84]
	call {vg_rsa_keygen_div}
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
2239:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2239b
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
2240:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2240b
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
2241:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2241b
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
2242:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2242b
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
2243:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2243b
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
	jne 2244f
	jmp 2245f
2244:
2246:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2246b
2245:
	and edi, 15
	jne 2247f
	jmp 2248f
2247:
2249:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2249b
2248:
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
2250:
	cmp edx, 32
	jae 2251f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2252f
2251:
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
2252:
	cmp edx, 0
	jne 2250b
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
2253:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2253b
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
2254:
	cmp edx, 32
	jae 2255f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2256f
2255:
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
2256:
	cmp edx, 0
	jne 2254b
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
2257:
	cmp edx, 32
	jae 2258f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2259f
2258:
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
2259:
	cmp edx, 0
	jne 2257b
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
	jne 2260f
	jmp 2261f
2260:
2262:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2262b
2261:
	and edi, 15
	jne 2263f
	jmp 2264f
2263:
2265:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2265b
2264:
	mov edi, DWORD PTR [esp+84]
2175:
	jmp 2173f
2172:
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
	jne 2266f
	jmp 2267f
2266:
2268:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2268b
2267:
	and edi, 15
	jne 2269f
	jmp 2270f
2269:
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
2270:
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
2272:
	cmp edx, 32
	jae 2273f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2274f
2273:
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
2274:
	cmp edx, 0
	jne 2272b
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
2275:
	cmp edx, 32
	jae 2276f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
2277:
	cmp edx, 0
	jne 2275b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+92], ebx
	mov eax, 1
	sub eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+88], eax
2173:
	jmp 2171f
2170:
	mov eax, 0
	mov DWORD PTR [edi+88], eax
2171:
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
2278:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2278b
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
2279:
	cmp edx, 32
	jae 2280f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2281f
2280:
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
2281:
	cmp edx, 0
	jne 2279b
	mov edi, DWORD PTR [esp+84]
	mov ebx, ecx
	and ebx, 1
	mov eax, DWORD PTR [edi+88]
	and eax, ebx
	cmp eax, 0
	jne 2282f
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
2284:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2284b
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
2285:
	cmp edx, 32
	jae 2286f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2287f
2286:
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
2287:
	cmp edx, 0
	jne 2285b
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
	jne 2288f
	jmp 2289f
2288:
2290:
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
	jne 2290b
2289:
	and edx, 15
	jne 2291f
	jmp 2292f
2291:
2293:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2293b
2292:
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
2294:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2294b
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
2295:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2295b
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
2296:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2296b
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
	jne 2297f
	jmp 2298f
2297:
2299:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2299b
2298:
	and edi, 15
	jne 2300f
	jmp 2301f
2300:
2302:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2302b
2301:
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
2303:
	cmp edx, 32
	jae 2304f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2305f
2304:
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
2305:
	cmp edx, 0
	jne 2303b
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
2306:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2306b
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
2307:
	cmp edx, 32
	jae 2308f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2309f
2308:
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
2309:
	cmp edx, 0
	jne 2307b
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
2310:
	cmp edx, 32
	jae 2311f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2312f
2311:
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
2312:
	cmp edx, 0
	jne 2310b
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
2313:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2313b
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
2314:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2314b
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
2315:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2315b
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
2316:
	cmp edx, 32
	jae 2317f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2318f
2317:
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
2318:
	cmp edx, 0
	jne 2316b
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
2319:
	cmp edx, 32
	jae 2320f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2321f
2320:
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
2321:
	cmp edx, 0
	jne 2319b
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
	jne 2322f
	jmp 2323f
2322:
2324:
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
	jne 2324b
2323:
	and edx, 15
	jne 2325f
	jmp 2326f
2325:
2327:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2327b
2326:
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
2328:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2328b
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
2329:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2329b
	mov edi, DWORD PTR [esp+84]
	call {vg_rsa_keygen_div}
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
2330:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2330b
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
2331:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2331b
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
2332:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2332b
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
2333:
	cmp edx, 32
	jae 2334f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2335f
2334:
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
2335:
	cmp edx, 0
	jne 2333b
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
2345:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2345b
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
	call {vg_rsa_keygen_div}
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
2348:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2348b
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
2349:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2349b
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
2350:
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
2351:
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
	jne 2351b
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
	jne 2350b
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
2352:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2352b
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
2353:
	cmp edx, 32
	jae 2354f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2355f
2354:
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
2355:
	cmp edx, 0
	jne 2353b
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
	jmp 2283f
2282:
	mov eax, 0
	mov DWORD PTR [edi+88], eax
	mov eax, 2
	mov DWORD PTR [edi+96], eax
2283:
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
2356:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2356b
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
	jne 2357f
	jmp 2358f
2357:
2359:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2359b
2358:
	and edi, 15
	jne 2360f
	jmp 2361f
2360:
2362:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2362b
2361:
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
2363:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2363b
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
	jne 2364f
	jmp 2365f
2364:
2366:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2366b
2365:
	and edi, 15
	jne 2367f
	jmp 2368f
2367:
2369:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2369b
2368:
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
2370:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2370b
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
	jne 2371f
	jmp 2372f
2371:
2373:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2373b
2372:
	and edi, 15
	jne 2374f
	jmp 2375f
2374:
2376:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2376b
2375:
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
2377:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2377b
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
	jne 2378f
	jmp 2379f
2378:
2380:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2380b
2379:
	and edi, 15
	jne 2381f
	jmp 2382f
2381:
2383:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2383b
2382:
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
2384:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2384b
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
	jne 2385f
	jmp 2386f
2385:
2387:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2387b
2386:
	and edi, 15
	jne 2388f
	jmp 2389f
2388:
2390:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2390b
2389:
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
2391:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2391b
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
2398:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2398b
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
	jne 2399f
	jmp 2400f
2399:
2401:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2401b
2400:
	and edi, 15
	jne 2402f
	jmp 2403f
2402:
2404:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2404b
2403:
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
2405:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2405b
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
