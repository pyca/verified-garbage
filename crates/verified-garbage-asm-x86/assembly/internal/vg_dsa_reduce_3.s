// The functions of `src/internal/vg_dsa_reduce_3.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_reduce_3:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+8], ebx
	mov DWORD PTR [eax+12], esi
	mov DWORD PTR [eax+16], ebp
	mov DWORD PTR [eax+20], edi
	mov edi, eax
	mov eax, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ecx
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
	mov esi, DWORD PTR [edi+28]
	mov eax, 0
	mov ebp, edi
21:
	mov DWORD PTR [ebp+400], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 21b
	mov eax, 0
	mov ebp, edi
22:
	mov DWORD PTR [ebp+456], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 22b
	mov ebx, DWORD PTR [edi+24]
	add ebx, esi
	cmp esi, ebx
	je 23f
25:
	movzx eax, BYTE PTR [esi]
	mov DWORD PTR [edi+456], eax
	mov ecx, 0
	mov ebp, edi
26:
	mov eax, DWORD PTR [ebp+400]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+400]
	mov DWORD PTR [ebp+176], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 26b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
27:
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
	jne 27b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
28:
	mov eax, DWORD PTR [ebp+176]
	mov edx, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+400], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 28b
	mov ecx, 0
	mov ebp, edi
29:
	mov eax, DWORD PTR [ebp+400]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+400]
	mov DWORD PTR [ebp+176], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 29b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
210:
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
	jne 210b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
211:
	mov eax, DWORD PTR [ebp+176]
	mov edx, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+400], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 211b
	mov ecx, 0
	mov ebp, edi
212:
	mov eax, DWORD PTR [ebp+400]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+400]
	mov DWORD PTR [ebp+176], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 212b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
213:
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
	jne 213b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
214:
	mov eax, DWORD PTR [ebp+176]
	mov edx, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+400], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 214b
	mov ecx, 0
	mov ebp, edi
215:
	mov eax, DWORD PTR [ebp+400]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+400]
	mov DWORD PTR [ebp+176], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 215b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
216:
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
	jne 216b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
217:
	mov eax, DWORD PTR [ebp+176]
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
	mov ecx, 0
	mov ebp, edi
218:
	mov eax, DWORD PTR [ebp+400]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+400]
	mov DWORD PTR [ebp+176], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 218b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
219:
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
	jne 219b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
220:
	mov eax, DWORD PTR [ebp+176]
	mov edx, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+400], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 220b
	mov ecx, 0
	mov ebp, edi
221:
	mov eax, DWORD PTR [ebp+400]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+400]
	mov DWORD PTR [ebp+176], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 221b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
222:
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
	jne 222b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
223:
	mov eax, DWORD PTR [ebp+176]
	mov edx, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+400], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 223b
	mov ecx, 0
	mov ebp, edi
224:
	mov eax, DWORD PTR [ebp+400]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+400]
	mov DWORD PTR [ebp+176], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 224b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
225:
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
	jne 225b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
226:
	mov eax, DWORD PTR [ebp+176]
	mov edx, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+400], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 226b
	mov ecx, 0
	mov ebp, edi
227:
	mov eax, DWORD PTR [ebp+400]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+400]
	mov DWORD PTR [ebp+176], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 227b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
228:
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
	jne 228b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
229:
	mov eax, DWORD PTR [ebp+176]
	mov edx, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+400], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 229b
	mov ecx, 0
	mov ebp, edi
230:
	mov eax, DWORD PTR [ebp+400]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+456]
	mov DWORD PTR [ebp+176], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 230b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
231:
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
	jne 231b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
232:
	mov eax, DWORD PTR [ebp+176]
	mov edx, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+400], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 232b
	add esi, 1
	cmp esi, ebx
	jne 25b
	jmp 24f
23:
24:
	mov ebx, DWORD PTR [edi+8]
	mov esi, DWORD PTR [edi+12]
	mov ebp, DWORD PTR [edi+16]
	mov edi, DWORD PTR [edi+20]
	ret
	.p2align 6
