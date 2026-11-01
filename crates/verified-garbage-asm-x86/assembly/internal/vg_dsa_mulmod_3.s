// The functions of `src/internal/vg_dsa_mulmod_3.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_mulmod_3:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+8], ebx
	mov DWORD PTR [eax+12], esi
	mov DWORD PTR [eax+16], ebp
	mov DWORD PTR [eax+20], edi
	mov edi, eax
	mov ebx, DWORD PTR [edi+64]
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
	mov DWORD PTR [edi], eax
	mov eax, 0
	mov ebp, edi
20:
	mov DWORD PTR [ebp+232], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 20b
	mov eax, 1
	mov DWORD PTR [edi+232], eax
	mov eax, 0
	mov ebp, edi
21:
	mov DWORD PTR [ebp+288], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 21b
	mov eax, 1
	mov DWORD PTR [edi+288], eax
	mov esi, 384
22:
	mov ecx, 0
	mov ebp, edi
23:
	mov eax, DWORD PTR [ebp+288]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+288]
	mov DWORD PTR [ebp+176], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 23b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
24:
	mov eax, DWORD PTR [ebp+176]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+120], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 24b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
25:
	mov eax, DWORD PTR [ebp+176]
	mov edx, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+288], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 25b
	sub esi, 1
	cmp esi, 0
	jne 22b
	mov eax, 0
	mov ebp, edi
26:
	mov DWORD PTR [ebp+176], eax
	add ebp, 4
	mov edx, edi
	add edx, 52
	cmp ebp, edx
	jne 26b
	mov ebp, edi
27:
	mov eax, DWORD PTR [ebp+344]
	mov DWORD PTR [edi+120], eax
	mov ebx, 0
	mov ecx, edi
28:
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [ecx+288]
	mul edx
	add eax, DWORD PTR [ebp+176]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+176], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [ecx+292]
	mul edx
	add eax, DWORD PTR [ebp+180]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+180], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 24
	cmp ecx, eax
	jne 28b
	sub ebp, 24
	mov eax, DWORD PTR [ebp+200]
	add eax, ebx
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [ebp+204]
	adc eax, 0
	mov DWORD PTR [ebp+204], eax
	mov eax, DWORD PTR [ebp+176]
	mov edx, DWORD PTR [edi]
	mul edx
	mov DWORD PTR [edi+120], eax
	mov ebx, 0
	mov ecx, edi
29:
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	add eax, DWORD PTR [ebp+176]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+176], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	add eax, DWORD PTR [ebp+180]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+180], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 24
	cmp ecx, eax
	jne 29b
	sub ebp, 24
	mov eax, DWORD PTR [ebp+200]
	add eax, ebx
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [ebp+204]
	adc eax, 0
	mov DWORD PTR [ebp+204], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 27b
	mov ecx, 0
	mov ebp, edi
210:
	mov eax, DWORD PTR [ebp+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+120], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 210b
	mov eax, DWORD PTR [edi+224]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
211:
	mov eax, DWORD PTR [ebp+200]
	mov edx, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+456], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 211b
	mov eax, 0
	mov ebp, edi
212:
	mov DWORD PTR [ebp+176], eax
	add ebp, 4
	mov edx, edi
	add edx, 52
	cmp ebp, edx
	jne 212b
	mov ebp, edi
213:
	mov eax, DWORD PTR [ebp+512]
	mov DWORD PTR [edi+120], eax
	mov ebx, 0
	mov ecx, edi
214:
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [ecx+456]
	mul edx
	add eax, DWORD PTR [ebp+176]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+176], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [ecx+460]
	mul edx
	add eax, DWORD PTR [ebp+180]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+180], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 24
	cmp ecx, eax
	jne 214b
	sub ebp, 24
	mov eax, DWORD PTR [ebp+200]
	add eax, ebx
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [ebp+204]
	adc eax, 0
	mov DWORD PTR [ebp+204], eax
	mov eax, DWORD PTR [ebp+176]
	mov edx, DWORD PTR [edi]
	mul edx
	mov DWORD PTR [edi+120], eax
	mov ebx, 0
	mov ecx, edi
215:
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	add eax, DWORD PTR [ebp+176]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+176], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	add eax, DWORD PTR [ebp+180]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+180], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 24
	cmp ecx, eax
	jne 215b
	sub ebp, 24
	mov eax, DWORD PTR [ebp+200]
	add eax, ebx
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [ebp+204]
	adc eax, 0
	mov DWORD PTR [ebp+204], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 213b
	mov ecx, 0
	mov ebp, edi
216:
	mov eax, DWORD PTR [ebp+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+120], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 216b
	mov eax, DWORD PTR [edi+224]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
217:
	mov eax, DWORD PTR [ebp+200]
	mov edx, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+400], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 217b
	mov ebx, DWORD PTR [edi+8]
	mov esi, DWORD PTR [edi+12]
	mov ebp, DWORD PTR [edi+16]
	mov edi, DWORD PTR [edi+20]
	ret
	.p2align 6
