// The functions of `src/internal/vg_rsa_keygen_candidate.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_keygen_candidate:
	push ebx
	push ebp
	push esi
	push edi
	mov edi, DWORD PTR [esp+56]
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
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+44], eax
	mov esi, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	mov eax, 0
20:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [edi+32]
	cmp eax, DWORD PTR [edi+4]
	jb 21f
	mov esi, DWORD PTR [edi+28]
	mov edx, DWORD PTR [edi+4]
	add edx, 16
	mov ebx, 0
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	add ebx, 256
	mov ecx, DWORD PTR [edi+4]
	add ebx, ecx
	sub ebx, 4
	shr ecx, 2
23:
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [ebx], eax
	add esi, 4
	sub ebx, 4
	sub ecx, 1
	jne 23b
	mov eax, DWORD PTR [edi+256]
	or eax, 1
	mov DWORD PTR [edi+256], eax
	mov ebx, DWORD PTR [edi+4]
	add ebx, edi
	mov eax, DWORD PTR [ebx+252]
	or eax, -1073741824
	mov DWORD PTR [ebx+252], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+152], eax
	mov eax, 0
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+24]
	cmp eax, 0
	je 24f
	mov esi, DWORD PTR [edi+20]
	mov edx, DWORD PTR [edi+4]
	add edx, 16
	mov ebx, 0
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	add ebx, 256
	mov ecx, DWORD PTR [edi+4]
	add ebx, ecx
	sub ebx, 4
	shr ecx, 2
26:
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [ebx], eax
	add esi, 4
	sub ebx, 4
	sub ecx, 1
	jne 26b
	lea esp, [esp-20]
	mov DWORD PTR [esp], edi
	mov edx, DWORD PTR [edi+4]
	add edx, 16
	mov ebp, 0
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov edx, DWORD PTR [edi+4]
	add edx, 16
	mov ebx, 0
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	add ebx, 256
	mov edx, DWORD PTR [edi+4]
	add edx, 16
	mov eax, 0
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, edx
	add eax, eax
	add eax, edi
	add eax, 256
	mov edx, DWORD PTR [edi+4]
	mov edi, eax
	mov ecx, 0
27:
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 27b
	mov edi, DWORD PTR [esp]
	mov esi, ecx
	mov edx, DWORD PTR [edi+4]
	add edx, 16
	mov ebp, 0
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov edx, DWORD PTR [edi+4]
	add edx, 16
	mov ebx, 0
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	add ebx, 256
	mov edx, DWORD PTR [edi+4]
	add edx, 16
	mov eax, 0
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, edx
	add eax, eax
	add eax, edx
	add eax, edi
	add eax, 256
	mov edx, DWORD PTR [edi+4]
	mov edi, eax
	mov ecx, 0
28:
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 28b
	mov edi, DWORD PTR [esp]
	mov edx, DWORD PTR [edi+4]
	add edx, 16
	mov ebp, 0
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov edx, DWORD PTR [edi+4]
	add edx, 16
	mov ebx, 0
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edx
	add ebx, ebx
	add ebx, edi
	add ebx, 256
	mov edi, DWORD PTR [edi+4]
	mov ecx, esi
29:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 29b
	mov edi, DWORD PTR [esp]
	mov ebx, 0
	mov edx, DWORD PTR [edi+4]
	add edx, 16
	mov ebp, 0
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ecx, DWORD PTR [edi+4]
	shr ecx, 2
	sub ecx, 4
210:
	or ebx, DWORD PTR [ebp]
	add ebp, 4
	sub ecx, 1
	jne 210b
	mov eax, DWORD PTR [ebp]
	mov ecx, eax
	shr ecx, 28
	and eax, 268435455
	or ebx, eax
	mov edx, DWORD PTR [ebp+4]
	or edx, DWORD PTR [ebp+8]
	or edx, DWORD PTR [ebp+12]
	mov eax, 1
	sub ebx, 1
	sbb eax, 0
	add ecx, eax
	mov eax, 0
	sub ecx, 2
	adc eax, 0
	mov ecx, 0
	sub edx, 1
	adc ecx, 0
	and eax, ecx
	lea esp, [esp+20]
	jmp 25f
24:
	mov eax, 0
25:
	cmp eax, 0
	jne 211f
	lea esp, [esp-20]
	mov edx, DWORD PTR [edi+4]
	add edi, 256
	mov DWORD PTR [esp], edi
	mov eax, edi
	add eax, edx
	mov DWORD PTR [esp+4], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_RSA_KEYGEN_TRIAL32}
	pop ecx
	mov DWORD PTR [esp+8], eax
	mov eax, edx
	cmp eax, 129
	sbb eax, eax
	and eax, -512
	add eax, 1024
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
213:
	mov edx, DWORD PTR [esp+8]
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov edi, DWORD PTR [esp]
	mov ebp, 0
214:
	mov eax, DWORD PTR [edi]
	add eax, ebp
	mov ebp, 0
	adc ebp, 0
	mov ecx, eax
	mul esi
	mul ebx
	add eax, ecx
	adc edx, ebp
	mov ebp, edx
	add edi, 4
	cmp edi, DWORD PTR [esp+4]
	jne 214b
	mov eax, 0
	mov edx, ebp
	sub edx, 1
	adc eax, 0
	sub ebp, ebx
	sub ebp, 1
	adc eax, 0
	mov DWORD PTR [esp+16], eax
	mov ecx, eax
	sub ecx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 8
	mov DWORD PTR [esp+8], edx
	mov eax, DWORD PTR [esp+12]
	sub eax, 1
	and eax, ecx
	mov DWORD PTR [esp+12], eax
	cmp eax, 0
	jne 213b
	mov eax, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp]
	sub edi, 256
	lea esp, [esp+20]
	cmp eax, 0
	jne 215f
	mov eax, 4
	jmp 216f
215:
	mov edx, DWORD PTR [edi+44]
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edx], eax
	mov eax, 0
	mov DWORD PTR [edx+4], eax
	mov eax, 3
216:
	jmp 212f
211:
	mov edx, DWORD PTR [edi+44]
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edx], eax
	mov eax, 0
	mov DWORD PTR [edx+4], eax
	mov eax, 2
212:
	cmp eax, 4
	je 217f
	jmp 218f
217:
	mov ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+4]
	add ebx, 16
	mov edx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edx
	add ebx, 256
	add ebx, edi
	mov esi, DWORD PTR [edi+4]
	shr esi, 2
	mov ecx, -1
219:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 219b
	mov ebx, DWORD PTR [edi+4]
	add ebx, 16
	mov edx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edx
	add ebx, 256
	add ebx, edi
	mov eax, DWORD PTR [ebx]
	sub eax, 1
	mov DWORD PTR [ebx], eax
	mov esi, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+16]
	mov eax, 0
	mov ebp, edi
220:
	mov DWORD PTR [ebp+128], eax
	add ebp, 4
	mov edx, edi
	add edx, 8
	cmp ebp, edx
	jne 220b
	mov ebx, edi
	add ebx, 128
	add esi, ecx
	sub esi, 1
221:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 221b
	mov eax, DWORD PTR [edi+128]
	and eax, 1
	cmp eax, 0
	je 222f
	mov eax, DWORD PTR [edi+128]
	xor eax, 1
	or eax, DWORD PTR [edi+132]
	cmp eax, 0
	je 224f
	mov eax, DWORD PTR [edi+128]
	xor eax, 65537
	or eax, DWORD PTR [edi+132]
	cmp eax, 0
	je 226f
	lea esp, [esp-20]
	mov eax, DWORD PTR [edi+4]
	add eax, 16
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, edx
	add eax, 256
	add eax, edi
	mov edx, DWORD PTR [edi+4]
	add eax, edx
	sub eax, 4
	mov DWORD PTR [esp], eax
	shr edx, 2
	mov DWORD PTR [esp+4], edx
	mov ecx, 0
	mov ebx, 0
228:
	mov eax, DWORD PTR [esp]
	mov esi, DWORD PTR [eax]
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	add esi, esi
	adc ecx, ecx
	adc ebx, ebx
	sbb ebp, ebp
	mov eax, ecx
	mov edx, ebx
	sub eax, DWORD PTR [edi+128]
	sbb edx, DWORD PTR [edi+132]
	adc ebp, 0
	sub ebp, 1
	xor eax, ecx
	and eax, ebp
	xor ecx, eax
	xor edx, ebx
	and edx, ebp
	xor ebx, edx
	mov eax, DWORD PTR [esp]
	sub eax, 4
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+4]
	sub eax, 1
	mov DWORD PTR [esp+4], eax
	cmp eax, 0
	jne 228b
	lea esp, [esp+20]
	mov eax, ecx
	mov edx, ebx
	mov DWORD PTR [edi+160], eax
	mov DWORD PTR [edi+164], edx
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+132]
	mov DWORD PTR [edi+176], eax
	mov DWORD PTR [edi+180], edx
	mov esi, 64
229:
	mov eax, DWORD PTR [edi+160]
	and eax, 1
	mov DWORD PTR [edi+100], eax
	mov ecx, 0
	mov ebp, edi
230:
	mov eax, DWORD PTR [ebp+160]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+176]
	mov DWORD PTR [ebp+336], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 8
	cmp ebp, edx
	jne 230b
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+104], ebx
	mov eax, DWORD PTR [edi+100]
	and eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+108], eax
	mov ecx, 0
	mov ebp, edi
231:
	mov eax, DWORD PTR [ebp+176]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+352], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 8
	cmp ebp, edx
	jne 231b
	mov ebx, ecx
	and ebx, 1
	mov ecx, 0
	sub ecx, DWORD PTR [edi+108]
	mov ebp, edi
232:
	mov eax, DWORD PTR [ebp+176]
	mov edx, DWORD PTR [ebp+160]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+240], eax
	add ebp, 4
	mov edx, edi
	add edx, 8
	cmp ebp, edx
	jne 232b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+108]
	mov ebp, edi
233:
	mov eax, DWORD PTR [ebp+336]
	mov edx, DWORD PTR [ebp+352]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+368], eax
	add ebp, 4
	mov edx, edi
	add edx, 8
	cmp ebp, edx
	jne 233b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+100]
	mov ebp, edi
234:
	mov eax, DWORD PTR [ebp+160]
	mov edx, DWORD PTR [ebp+368]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+224], eax
	add ebp, 4
	mov edx, edi
	add edx, 8
	cmp ebp, edx
	jne 234b
	mov ebx, 0
	mov DWORD PTR [edi+232], ebx
	mov ebp, edi
235:
	mov eax, DWORD PTR [ebp+228]
	and eax, 1
	ror eax, 1
	mov edx, DWORD PTR [ebp+224]
	shr edx, 1
	add edx, eax
	mov DWORD PTR [ebp+224], edx
	add ebp, 4
	mov edx, edi
	add edx, 8
	cmp ebp, edx
	jne 235b
	mov eax, 0
	and eax, 1
	ror eax, 1
	mov edx, DWORD PTR [edi+232]
	shr edx, 1
	add edx, eax
	mov DWORD PTR [edi+232], edx
	mov eax, DWORD PTR [edi+224]
	and eax, 1
	mov DWORD PTR [edi+100], eax
	mov ecx, 0
	mov ebp, edi
236:
	mov eax, DWORD PTR [ebp+224]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+240]
	mov DWORD PTR [ebp+336], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 8
	cmp ebp, edx
	jne 236b
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+104], ebx
	mov eax, DWORD PTR [edi+100]
	and eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+108], eax
	mov ecx, 0
	mov ebp, edi
237:
	mov eax, DWORD PTR [ebp+240]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+224]
	mov DWORD PTR [ebp+352], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 8
	cmp ebp, edx
	jne 237b
	mov ebx, ecx
	and ebx, 1
	mov ecx, 0
	sub ecx, DWORD PTR [edi+108]
	mov ebp, edi
238:
	mov eax, DWORD PTR [ebp+240]
	mov edx, DWORD PTR [ebp+224]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+176], eax
	add ebp, 4
	mov edx, edi
	add edx, 8
	cmp ebp, edx
	jne 238b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+108]
	mov ebp, edi
239:
	mov eax, DWORD PTR [ebp+336]
	mov edx, DWORD PTR [ebp+352]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+368], eax
	add ebp, 4
	mov edx, edi
	add edx, 8
	cmp ebp, edx
	jne 239b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+100]
	mov ebp, edi
240:
	mov eax, DWORD PTR [ebp+224]
	mov edx, DWORD PTR [ebp+368]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+160], eax
	add ebp, 4
	mov edx, edi
	add edx, 8
	cmp ebp, edx
	jne 240b
	mov ebx, 0
	mov DWORD PTR [edi+168], ebx
	mov ebp, edi
241:
	mov eax, DWORD PTR [ebp+164]
	and eax, 1
	ror eax, 1
	mov edx, DWORD PTR [ebp+160]
	shr edx, 1
	add edx, eax
	mov DWORD PTR [ebp+160], edx
	add ebp, 4
	mov edx, edi
	add edx, 8
	cmp ebp, edx
	jne 241b
	mov eax, 0
	and eax, 1
	ror eax, 1
	mov edx, DWORD PTR [edi+168]
	shr edx, 1
	add edx, eax
	mov DWORD PTR [edi+168], edx
	sub esi, 1
	cmp esi, 0
	jne 229b
	mov ebx, edi
	add ebx, 256
	mov ebp, DWORD PTR [edi+4]
	add ebp, 16
	mov edx, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, 256
	add ebp, edi
	mov esi, DWORD PTR [edi+4]
	shr esi, 2
	mov ecx, -1
242:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 242b
	mov eax, DWORD PTR [edi+256]
	add eax, 1
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+176]
	sub eax, 1
	or eax, DWORD PTR [edi+180]
	mov ecx, 0
	sub eax, 1
	adc ecx, 0
	mov eax, ecx
	jmp 227f
226:
	lea esp, [esp-20]
	mov eax, DWORD PTR [edi+4]
	add eax, 16
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, edx
	add eax, 256
	add eax, edi
	mov ecx, DWORD PTR [edi+4]
	mov DWORD PTR [esp], edi
	mov edi, eax
	add eax, ecx
	mov DWORD PTR [esp+4], eax
	mov ebx, 65537
	mov esi, 65535
	mov ebp, 0
243:
	mov eax, DWORD PTR [edi]
	add eax, ebp
	mov ebp, 0
	adc ebp, 0
	mov ecx, eax
	mul esi
	mul ebx
	add eax, ecx
	adc edx, ebp
	mov ebp, edx
	add edi, 4
	cmp edi, DWORD PTR [esp+4]
	jne 243b
	mov eax, 0
	mov edx, ebp
	sub edx, 1
	adc eax, 0
	sub ebp, ebx
	sub ebp, 1
	adc eax, 0
	xor eax, 1
	mov edi, DWORD PTR [esp]
	lea esp, [esp+20]
227:
	jmp 225f
224:
	mov eax, 1
225:
	jmp 223f
222:
	mov eax, 0
223:
	cmp eax, 0
	je 244f
	mov edx, DWORD PTR [edi+40]
	lea esp, [esp-28]
	mov DWORD PTR [esp+24], edx
	mov ecx, DWORD PTR [edi+4]
	mov eax, ecx
	shr eax, 3
	mov edx, 0
	mov DWORD PTR [edi+48], eax
	mov DWORD PTR [edi+52], edx
	add ecx, 16
	mov eax, ecx
	mov DWORD PTR [edi+224], eax
	mov DWORD PTR [edi+228], edx
	mov eax, edi
	add eax, 256
	mov DWORD PTR [edi+64], eax
	mov DWORD PTR [edi+68], edx
	add eax, ecx
	mov DWORD PTR [edi+72], eax
	mov DWORD PTR [edi+76], edx
	add eax, ecx
	mov DWORD PTR [edi+80], eax
	mov DWORD PTR [edi+84], edx
	add eax, ecx
	mov DWORD PTR [edi+88], eax
	mov DWORD PTR [edi+92], edx
	add eax, ecx
	mov DWORD PTR [edi+96], eax
	mov DWORD PTR [edi+100], edx
	add eax, ecx
	mov DWORD PTR [edi+104], eax
	mov DWORD PTR [edi+108], edx
	add eax, ecx
	mov DWORD PTR [edi+112], eax
	mov DWORD PTR [edi+116], edx
	add eax, ecx
	mov DWORD PTR [edi+120], eax
	mov DWORD PTR [edi+124], edx
	add eax, ecx
	mov ebx, DWORD PTR [edi+256]
	mov ecx, ebx
	mov eax, ebx
	mul ecx
	mov ebp, 2
	sub ebp, eax
	mov eax, ecx
	mul ebp
	mov ecx, eax
	mov eax, ebx
	mul ecx
	mov ebp, 2
	sub ebp, eax
	mov eax, ecx
	mul ebp
	mov ecx, eax
	mov eax, ebx
	mul ecx
	mov ebp, 2
	sub ebp, eax
	mov eax, ecx
	mul ebp
	mov ecx, eax
	mov eax, ebx
	mul ecx
	mov ebp, 2
	sub ebp, eax
	mov eax, ecx
	mul ebp
	mov ecx, eax
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+56], eax
	mov ebx, DWORD PTR [edi+256]
	mov esi, DWORD PTR [edi+260]
	mov ecx, DWORD PTR [edi+56]
	mov eax, ebx
	mul ecx
	add eax, 1
	adc edx, 0
	mov ebp, edx
	mov eax, esi
	mul ecx
	add eax, ebp
	mov ebp, eax
	mov eax, ecx
	mul ebp
	mov DWORD PTR [edi+60], eax
	mov ebp, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+48]
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, edx
	mov eax, 0
246:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 246b
	mov ebp, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+48]
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	sub ebp, 4
	mov eax, -2147483648
	mov DWORD PTR [ebp], eax
	lea esp, [esp-20]
	mov DWORD PTR [esp], edi
	mov esi, DWORD PTR [edi+48]
	add esi, 1
247:
	mov ebx, DWORD PTR [edi+112]
	mov ebp, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+48]
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
248:
	mov eax, DWORD PTR [ebx]
	add ecx, ecx
	adc eax, eax
	mov DWORD PTR [ebp], eax
	sbb ecx, ecx
	add ebx, 4
	add ebp, 4
	sub edx, 4
	jne 248b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [ebp], eax
	mov ebp, DWORD PTR [edi+80]
	mov ebx, DWORD PTR [edi+64]
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+48]
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
249:
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 249b
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edi, DWORD PTR [esp]
	mov ebp, DWORD PTR [edi+80]
	mov ebx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+48]
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, edx
250:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 250b
	mov edi, DWORD PTR [esp]
	sub esi, 1
	jne 247b
	lea esp, [esp+20]
	mov eax, 6
	mov ecx, 6
	mov edx, DWORD PTR [esp+24]
	push eax
	push ecx
	push ecx
	push edx
	push edi
	call {vg_rsa_mont_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 6
	mov ecx, 6
	mov edx, DWORD PTR [esp+24]
	push eax
	push ecx
	push ecx
	push edx
	push edi
	call {vg_rsa_mont_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 6
	mov ecx, 6
	mov edx, DWORD PTR [esp+24]
	push eax
	push ecx
	push ecx
	push edx
	push edi
	call {vg_rsa_mont_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 6
	mov ecx, 6
	mov edx, DWORD PTR [esp+24]
	push eax
	push ecx
	push ecx
	push edx
	push edi
	call {vg_rsa_mont_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 6
	mov ecx, 6
	mov edx, DWORD PTR [esp+24]
	push eax
	push ecx
	push ecx
	push edx
	push edi
	call {vg_rsa_mont_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 6
	mov ecx, 6
	mov edx, DWORD PTR [esp+24]
	push eax
	push ecx
	push ecx
	push edx
	push edi
	call {vg_rsa_mont_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, DWORD PTR [edi+96]
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
251:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 251b
	mov ebp, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+48]
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, edx
	mov eax, 0
252:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 252b
	mov ebp, DWORD PTR [edi+112]
	mov eax, 1
	mov DWORD PTR [ebp], eax
	mov eax, 4
	mov ecx, 6
	mov edx, DWORD PTR [esp+24]
	push eax
	push ecx
	push ecx
	push edx
	push edi
	call {vg_rsa_mont_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
253:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 253b
	lea esp, [esp-20]
	mov DWORD PTR [esp], edi
	mov ebp, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+224]
	mov ebx, 0
	add ebx, ebx
	add ebx, ebx
	add ebx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edx
	add ebx, edi
	add ebx, 256
	mov edx, DWORD PTR [edi+224]
	mov eax, 0
	add eax, eax
	add eax, eax
	add eax, edx
	add eax, eax
	add eax, eax
	add eax, edx
	add eax, eax
	add eax, edi
	add eax, 256
	mov edx, DWORD PTR [edi+48]
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
254:
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 254b
	mov edi, DWORD PTR [esp]
	lea esp, [esp+20]
	lea esp, [esp-20]
	mov ebx, 0
	mov esi, 0
	mov ebp, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+48]
	mov DWORD PTR [esp], edi
	mov edi, edx
255:
	mov eax, DWORD PTR [ebp]
	mov ecx, DWORD PTR [ebp+4]
	mov edx, ebx
	or edx, esi
	cmp edx, 1
	sbb edx, edx
	and eax, edx
	and ecx, edx
	or ebx, eax
	or esi, ecx
	add ebp, 8
	sub edi, 1
	jne 255b
	mov edi, DWORD PTR [esp]
	lea esp, [esp+20]
	mov eax, 0
	sub eax, ebx
	mov edx, 0
	sbb edx, esi
	and eax, ebx
	and edx, esi
	mov DWORD PTR [edi+136], eax
	mov DWORD PTR [edi+140], edx
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+64]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
256:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 256b
	mov eax, 0
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebp], eax
	mov ecx, -1
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov esi, DWORD PTR [edi+48]
	add esi, esi
257:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov edx, DWORD PTR [ebp]
	shr edx, 1
	add edx, eax
	mov ebx, DWORD PTR [ebp]
	xor edx, ebx
	and edx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp], ebx
	add ebp, 4
	sub esi, 1
	jne 257b
	mov eax, DWORD PTR [edi+136]
	or eax, DWORD PTR [edi+140]
	and eax, -572662307
	cmp eax, 1
	sbb ecx, ecx
	xor ecx, -1
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov esi, DWORD PTR [edi+48]
	add esi, esi
258:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov edx, DWORD PTR [ebp]
	shr edx, 1
	add edx, eax
	mov ebx, DWORD PTR [ebp]
	xor edx, ebx
	and edx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp], ebx
	add ebp, 4
	sub esi, 1
	jne 258b
	mov eax, DWORD PTR [edi+136]
	or eax, DWORD PTR [edi+140]
	and eax, -1717986919
	cmp eax, 1
	sbb ecx, ecx
	xor ecx, -1
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov esi, DWORD PTR [edi+48]
	add esi, esi
259:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov edx, DWORD PTR [ebp]
	shr edx, 1
	add edx, eax
	mov ebx, DWORD PTR [ebp]
	xor edx, ebx
	and edx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp], ebx
	add ebp, 4
	sub esi, 1
	jne 259b
	mov eax, DWORD PTR [edi+136]
	or eax, DWORD PTR [edi+140]
	and eax, 286331153
	cmp eax, 1
	sbb ecx, ecx
	xor ecx, -1
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov esi, DWORD PTR [edi+48]
	add esi, esi
260:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov edx, DWORD PTR [ebp]
	shr edx, 1
	add edx, eax
	mov ebx, DWORD PTR [ebp]
	xor edx, ebx
	and edx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp], ebx
	add ebp, 4
	sub esi, 1
	jne 260b
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+140]
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], edx
	mov eax, 0
	mov DWORD PTR [edi+176], eax
	mov DWORD PTR [edi+192], eax
	mov ecx, 3
	mov eax, DWORD PTR [edi+48]
	cmp eax, 59
	sbb eax, eax
	and eax, 1
	add ecx, eax
	mov eax, DWORD PTR [edi+48]
	cmp eax, 22
	sbb eax, eax
	and eax, 1
	add ecx, eax
	mov eax, DWORD PTR [edi+48]
	cmp eax, 8
	sbb eax, eax
	and eax, 1
	add ecx, eax
	mov eax, DWORD PTR [edi+48]
	cmp eax, 7
	sbb eax, eax
	and eax, 1
	add ecx, eax
	mov eax, DWORD PTR [edi+48]
	cmp eax, 6
	sbb eax, eax
	and eax, 1
	add ecx, eax
	mov eax, DWORD PTR [edi+48]
	cmp eax, 5
	sbb eax, eax
	and eax, 19
	add ecx, eax
	mov DWORD PTR [edi+200], ecx
261:
	mov edx, DWORD PTR [edi+48]
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [edi+32]
	sub eax, DWORD PTR [edi+152]
	cmp eax, edx
	jb 262f
	mov edx, DWORD PTR [edi+48]
	add edx, edx
	add edx, edx
	add edx, edx
	mov esi, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+152]
	add esi, eax
	add eax, edx
	mov DWORD PTR [edi+152], eax
	mov edx, DWORD PTR [edi+48]
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebx, DWORD PTR [edi+112]
	add ebx, edx
	sub ebx, 4
	mov ecx, DWORD PTR [edi+48]
	add ecx, ecx
264:
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [ebx], eax
	add esi, 4
	sub ebx, 4
	sub ecx, 1
	jne 264b
	mov ebp, DWORD PTR [edi+112]
	mov ebx, DWORD PTR [ebp]
	mov eax, ebx
	or eax, 1
	mov DWORD PTR [ebp], eax
	mov esi, DWORD PTR [edi+112]
	mov ebp, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+48]
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
265:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 265b
	mov ebp, DWORD PTR [edi+112]
	mov DWORD PTR [ebp], ebx
	mov esi, ecx
	mov ebx, 0
	mov ebp, DWORD PTR [edi+112]
	add ebp, 4
	mov ecx, DWORD PTR [edi+48]
	add ecx, ecx
	sub ecx, 1
266:
	or ebx, DWORD PTR [ebp]
	add ebp, 4
	sub ecx, 1
	jne 266b
	mov ebp, DWORD PTR [edi+112]
	mov eax, DWORD PTR [ebp]
	or eax, 1
	xor eax, 1
	or ebx, eax
	cmp ebx, 1
	sbb ebx, ebx
	xor ebx, -1
	mov eax, esi
	and eax, ebx
	mov ebp, DWORD PTR [edi+112]
	mov ecx, eax
	xor ecx, -1
	and ecx, 2
	or ecx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], ecx
	mov edx, DWORD PTR [edi+48]
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebx, ebp
	add ebx, edx
	sub ebx, 4
	mov ecx, eax
	xor ecx, -1
	and ecx, -2147483648
	xor ecx, -1
	and ecx, DWORD PTR [ebx]
	mov DWORD PTR [ebx], ecx
	mov DWORD PTR [edi+144], eax
	mov eax, 4
	mov ecx, 6
	mov edx, DWORD PTR [esp+24]
	push eax
	push ecx
	push ecx
	push edx
	push edi
	call {vg_rsa_mont_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, DWORD PTR [edi+104]
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
267:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 267b
	mov edx, DWORD PTR [esp+24]
	push edx
	push edi
	call {vg_miller_rabin_round}
	pop ecx
	pop ecx
	mov esi, eax
	mov eax, DWORD PTR [edi+176]
	add eax, 1
	mov DWORD PTR [edi+176], eax
	mov ebx, DWORD PTR [edi+144]
	and ebx, 1
	add ebx, DWORD PTR [edi+192]
	mov DWORD PTR [edi+192], ebx
	mov edx, DWORD PTR [edi+200]
	cmp eax, 16
	sbb ecx, ecx
	cmp ebx, edx
	sbb edx, edx
	or ecx, edx
	and ecx, 3
	add ecx, 1
	mov ebp, 0
	sub ebp, esi
	and ecx, ebp
	xor ebp, -1
	and ebp, 3
	or ecx, ebp
	mov DWORD PTR [edi+168], ecx
	jmp 263f
262:
	mov eax, 0
	mov DWORD PTR [edi+168], eax
263:
	mov eax, DWORD PTR [edi+168]
	cmp eax, 4
	je 261b
	lea esp, [esp+28]
	mov eax, DWORD PTR [edi+168]
	cmp eax, 1
	je 268f
	cmp eax, 0
	je 270f
	mov edx, DWORD PTR [edi+44]
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edx], eax
	mov eax, 0
	mov DWORD PTR [edx+4], eax
	mov eax, 3
	jmp 271f
270:
	mov edx, DWORD PTR [edi+44]
	mov eax, 0
	mov DWORD PTR [edx], eax
	mov eax, 0
	mov DWORD PTR [edx+4], eax
271:
	jmp 269f
268:
	mov ebx, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	mov esi, edi
	add esi, 256
	add esi, ecx
	sub esi, 1
272:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 272b
	mov edx, DWORD PTR [edi+44]
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edx], eax
	mov eax, 0
	mov DWORD PTR [edx+4], eax
	mov eax, 1
269:
	jmp 245f
244:
	mov edx, DWORD PTR [edi+44]
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edx], eax
	mov eax, 0
	mov DWORD PTR [edx+4], eax
	mov eax, 3
245:
218:
	jmp 22f
21:
	mov edx, DWORD PTR [edi+44]
	mov eax, 0
	mov DWORD PTR [edx], eax
	mov eax, 0
	mov DWORD PTR [edx+4], eax
22:
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
