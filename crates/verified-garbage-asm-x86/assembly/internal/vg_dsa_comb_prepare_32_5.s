// The functions of `src/internal/vg_dsa_comb_prepare_32_5.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_comb_prepare_32_5:
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
	mov DWORD PTR [ebp+1624], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 20b
	mov eax, 1
	mov DWORD PTR [edi+1624], eax
	mov eax, DWORD PTR [edi+316]
	shr eax, 31
	cmp eax, 1
	je 21f
	mov eax, 0
	mov ebp, edi
23:
	mov DWORD PTR [ebp+2144], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 23b
	mov eax, 1
	mov DWORD PTR [edi+2144], eax
	mov esi, 2080
24:
	mov ecx, 0
	mov ebp, edi
25:
	mov eax, DWORD PTR [ebp+2144]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+2144]
	mov DWORD PTR [ebp+1104], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 25b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+1360], eax
	mov ecx, 0
	mov ebp, edi
26:
	mov eax, DWORD PTR [ebp+1104]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+584], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 26b
	mov eax, DWORD PTR [edi+1360]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
27:
	mov eax, DWORD PTR [ebp+1104]
	mov edx, DWORD PTR [ebp+584]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+2144], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 27b
	sub esi, 1
	cmp esi, 0
	jne 24b
	jmp 22f
21:
	mov eax, 0
	mov ebp, edi
28:
	mov DWORD PTR [ebp+2144], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 28b
	mov eax, -2147483648
	mov DWORD PTR [edi+2396], eax
	mov esi, 33
29:
	mov ecx, 0
	mov ebp, edi
210:
	mov eax, DWORD PTR [ebp+2144]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+2144]
	mov DWORD PTR [ebp+1104], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 210b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+1360], eax
	mov ecx, 0
	mov ebp, edi
211:
	mov eax, DWORD PTR [ebp+1104]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+584], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 211b
	mov eax, DWORD PTR [edi+1360]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
212:
	mov eax, DWORD PTR [ebp+1104]
	mov edx, DWORD PTR [ebp+584]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+2144], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 212b
	sub esi, 1
	cmp esi, 0
	jne 29b
22:
	mov esi, 6
213:
	mov eax, 0
	mov ebp, edi
214:
	mov DWORD PTR [ebp+1104], eax
	add ebp, 4
	mov edx, edi
	add edx, 516
	cmp ebp, edx
	jne 214b
	mov ebp, edi
215:
	mov eax, DWORD PTR [ebp+2144]
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
216:
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+2144]
	mul edx
	add eax, DWORD PTR [ebp+1104]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+2148]
	mul edx
	add eax, DWORD PTR [ebp+1108]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1108], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 256
	cmp ecx, eax
	jne 216b
	sub ebp, 256
	mov eax, DWORD PTR [ebp+1360]
	add eax, ebx
	mov DWORD PTR [ebp+1360], eax
	mov eax, DWORD PTR [ebp+1364]
	adc eax, 0
	mov DWORD PTR [ebp+1364], eax
	mov eax, DWORD PTR [ebp+1104]
	mov edx, DWORD PTR [edi]
	mul edx
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
217:
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	add eax, DWORD PTR [ebp+1104]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	add eax, DWORD PTR [ebp+1108]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1108], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 256
	cmp ecx, eax
	jne 217b
	sub ebp, 256
	mov eax, DWORD PTR [ebp+1360]
	add eax, ebx
	mov DWORD PTR [ebp+1360], eax
	mov eax, DWORD PTR [ebp+1364]
	adc eax, 0
	mov DWORD PTR [ebp+1364], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 215b
	mov ecx, 0
	mov ebp, edi
218:
	mov eax, DWORD PTR [ebp+1360]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+584], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 218b
	mov eax, DWORD PTR [edi+1616]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
219:
	mov eax, DWORD PTR [ebp+1360]
	mov edx, DWORD PTR [ebp+584]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+2144], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 219b
	sub esi, 1
	cmp esi, 0
	jne 213b
	mov ecx, 0
	mov ebp, edi
220:
	mov eax, DWORD PTR [ebp+64]
	mov edx, DWORD PTR [ebp+64]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+16384], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 220b
	mov ecx, 0
	mov ebp, edi
221:
	mov eax, DWORD PTR [ebp+2144]
	mov edx, DWORD PTR [ebp+2144]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+16640], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 221b
	mov eax, 0
	mov ebp, edi
222:
	mov DWORD PTR [ebp+1104], eax
	add ebp, 4
	mov edx, edi
	add edx, 516
	cmp ebp, edx
	jne 222b
	mov ebp, edi
223:
	mov eax, DWORD PTR [ebp+2144]
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
224:
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+1624]
	mul edx
	add eax, DWORD PTR [ebp+1104]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+1628]
	mul edx
	add eax, DWORD PTR [ebp+1108]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1108], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 256
	cmp ecx, eax
	jne 224b
	sub ebp, 256
	mov eax, DWORD PTR [ebp+1360]
	add eax, ebx
	mov DWORD PTR [ebp+1360], eax
	mov eax, DWORD PTR [ebp+1364]
	adc eax, 0
	mov DWORD PTR [ebp+1364], eax
	mov eax, DWORD PTR [ebp+1104]
	mov edx, DWORD PTR [edi]
	mul edx
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
225:
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	add eax, DWORD PTR [ebp+1104]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	add eax, DWORD PTR [ebp+1108]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1108], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 256
	cmp ecx, eax
	jne 225b
	sub ebp, 256
	mov eax, DWORD PTR [ebp+1360]
	add eax, ebx
	mov DWORD PTR [ebp+1360], eax
	mov eax, DWORD PTR [ebp+1364]
	adc eax, 0
	mov DWORD PTR [ebp+1364], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 223b
	mov ecx, 0
	mov ebp, edi
226:
	mov eax, DWORD PTR [ebp+1360]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+584], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 226b
	mov eax, DWORD PTR [edi+1616]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
227:
	mov eax, DWORD PTR [ebp+1360]
	mov edx, DWORD PTR [ebp+584]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+3184], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 227b
	mov eax, 0
	mov ebp, edi
228:
	mov DWORD PTR [ebp+1104], eax
	add ebp, 4
	mov edx, edi
	add edx, 516
	cmp ebp, edx
	jne 228b
	mov ebp, edi
229:
	mov eax, DWORD PTR [ebp+2664]
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
230:
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+2144]
	mul edx
	add eax, DWORD PTR [ebp+1104]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+2148]
	mul edx
	add eax, DWORD PTR [ebp+1108]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1108], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 256
	cmp ecx, eax
	jne 230b
	sub ebp, 256
	mov eax, DWORD PTR [ebp+1360]
	add eax, ebx
	mov DWORD PTR [ebp+1360], eax
	mov eax, DWORD PTR [ebp+1364]
	adc eax, 0
	mov DWORD PTR [ebp+1364], eax
	mov eax, DWORD PTR [ebp+1104]
	mov edx, DWORD PTR [edi]
	mul edx
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
231:
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	add eax, DWORD PTR [ebp+1104]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	add eax, DWORD PTR [ebp+1108]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1108], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 256
	cmp ecx, eax
	jne 231b
	sub ebp, 256
	mov eax, DWORD PTR [ebp+1360]
	add eax, ebx
	mov DWORD PTR [ebp+1360], eax
	mov eax, DWORD PTR [ebp+1364]
	adc eax, 0
	mov DWORD PTR [ebp+1364], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 229b
	mov ecx, 0
	mov ebp, edi
232:
	mov eax, DWORD PTR [ebp+1360]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+584], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 232b
	mov eax, DWORD PTR [edi+1616]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
233:
	mov eax, DWORD PTR [ebp+1360]
	mov edx, DWORD PTR [ebp+584]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+2664], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 233b
	mov ecx, 0
	mov ebp, edi
234:
	mov eax, DWORD PTR [ebp+3184]
	mov edx, DWORD PTR [ebp+3184]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+16896], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 234b
	mov ecx, 0
	mov ebp, edi
235:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, DWORD PTR [ebp+2664]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+17152], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 235b
	mov eax, 1
	mov DWORD PTR [edi+28], eax
236:
	mov esi, 32
237:
	mov eax, 0
	mov ebp, edi
238:
	mov DWORD PTR [ebp+1104], eax
	add ebp, 4
	mov edx, edi
	add edx, 516
	cmp ebp, edx
	jne 238b
	mov ebp, edi
239:
	mov eax, DWORD PTR [ebp+2664]
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
240:
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+2664]
	mul edx
	add eax, DWORD PTR [ebp+1104]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+2668]
	mul edx
	add eax, DWORD PTR [ebp+1108]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1108], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 256
	cmp ecx, eax
	jne 240b
	sub ebp, 256
	mov eax, DWORD PTR [ebp+1360]
	add eax, ebx
	mov DWORD PTR [ebp+1360], eax
	mov eax, DWORD PTR [ebp+1364]
	adc eax, 0
	mov DWORD PTR [ebp+1364], eax
	mov eax, DWORD PTR [ebp+1104]
	mov edx, DWORD PTR [edi]
	mul edx
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
241:
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	add eax, DWORD PTR [ebp+1104]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	add eax, DWORD PTR [ebp+1108]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1108], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 256
	cmp ecx, eax
	jne 241b
	sub ebp, 256
	mov eax, DWORD PTR [ebp+1360]
	add eax, ebx
	mov DWORD PTR [ebp+1360], eax
	mov eax, DWORD PTR [ebp+1364]
	adc eax, 0
	mov DWORD PTR [ebp+1364], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 239b
	mov ecx, 0
	mov ebp, edi
242:
	mov eax, DWORD PTR [ebp+1360]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+584], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 242b
	mov eax, DWORD PTR [edi+1616]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
243:
	mov eax, DWORD PTR [ebp+1360]
	mov edx, DWORD PTR [ebp+584]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+2664], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 243b
	sub esi, 1
	cmp esi, 0
	jne 237b
	mov esi, DWORD PTR [edi+28]
	add esi, esi
	mov DWORD PTR [edi+28], esi
	mov eax, esi
	mov edx, 256
	mul edx
	add eax, edi
	add eax, 16896
	mov ecx, eax
	mov ebp, edi
	mov ebx, 64
244:
	mov eax, DWORD PTR [ebp+2664]
	mov DWORD PTR [ecx], eax
	add ecx, 4
	add ebp, 4
	sub ebx, 1
	jne 244b
	cmp esi, 16
	jne 236b
	mov esi, 1
245:
	mov eax, 0
	sub eax, esi
	and eax, esi
	mov DWORD PTR [edi+28], eax
	mov edx, esi
	sub edx, eax
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+4]
	mov edx, 256
	mul edx
	add eax, edi
	add eax, 16896
	mov ecx, eax
	mov ebp, edi
	mov ebx, 64
246:
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [ebp+3184], eax
	add ecx, 4
	add ebp, 4
	sub ebx, 1
	jne 246b
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+4]
	mov edx, 256
	mul edx
	add eax, edi
	add eax, 16896
	mov ecx, eax
	mov ebp, edi
	mov ebx, 64
247:
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [ebp+2664], eax
	add ecx, 4
	add ebp, 4
	sub ebx, 1
	jne 247b
	mov eax, 0
	mov ebp, edi
248:
	mov DWORD PTR [ebp+1104], eax
	add ebp, 4
	mov edx, edi
	add edx, 516
	cmp ebp, edx
	jne 248b
	mov ebp, edi
249:
	mov eax, DWORD PTR [ebp+3184]
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
250:
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+2664]
	mul edx
	add eax, DWORD PTR [ebp+1104]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+2668]
	mul edx
	add eax, DWORD PTR [ebp+1108]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1108], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 256
	cmp ecx, eax
	jne 250b
	sub ebp, 256
	mov eax, DWORD PTR [ebp+1360]
	add eax, ebx
	mov DWORD PTR [ebp+1360], eax
	mov eax, DWORD PTR [ebp+1364]
	adc eax, 0
	mov DWORD PTR [ebp+1364], eax
	mov eax, DWORD PTR [ebp+1104]
	mov edx, DWORD PTR [edi]
	mul edx
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
251:
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	add eax, DWORD PTR [ebp+1104]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	add eax, DWORD PTR [ebp+1108]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1108], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 256
	cmp ecx, eax
	jne 251b
	sub ebp, 256
	mov eax, DWORD PTR [ebp+1360]
	add eax, ebx
	mov DWORD PTR [ebp+1360], eax
	mov eax, DWORD PTR [ebp+1364]
	adc eax, 0
	mov DWORD PTR [ebp+1364], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 249b
	mov ecx, 0
	mov ebp, edi
252:
	mov eax, DWORD PTR [ebp+1360]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+584], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 252b
	mov eax, DWORD PTR [edi+1616]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
253:
	mov eax, DWORD PTR [ebp+1360]
	mov edx, DWORD PTR [ebp+584]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+3704], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 253b
	mov eax, esi
	mov edx, 256
	mul edx
	add eax, edi
	add eax, 16896
	mov ecx, eax
	mov ebp, edi
	mov ebx, 64
254:
	mov eax, DWORD PTR [ebp+3704]
	mov DWORD PTR [ecx], eax
	add ecx, 4
	add ebp, 4
	sub ebx, 1
	jne 254b
	add esi, 1
	cmp esi, 32
	jne 245b
	mov ecx, 0
	mov ebp, edi
255:
	mov eax, DWORD PTR [ebp+16896]
	mov edx, DWORD PTR [ebp+16896]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+3184], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 255b
	mov esi, 32
256:
	mov eax, 0
	mov ebp, edi
257:
	mov DWORD PTR [ebp+1104], eax
	add ebp, 4
	mov edx, edi
	add edx, 516
	cmp ebp, edx
	jne 257b
	mov ebp, edi
258:
	mov eax, DWORD PTR [ebp+3184]
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
259:
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+3184]
	mul edx
	add eax, DWORD PTR [ebp+1104]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+3188]
	mul edx
	add eax, DWORD PTR [ebp+1108]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1108], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 256
	cmp ecx, eax
	jne 259b
	sub ebp, 256
	mov eax, DWORD PTR [ebp+1360]
	add eax, ebx
	mov DWORD PTR [ebp+1360], eax
	mov eax, DWORD PTR [ebp+1364]
	adc eax, 0
	mov DWORD PTR [ebp+1364], eax
	mov eax, DWORD PTR [ebp+1104]
	mov edx, DWORD PTR [edi]
	mul edx
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
260:
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	add eax, DWORD PTR [ebp+1104]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	add eax, DWORD PTR [ebp+1108]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1108], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 256
	cmp ecx, eax
	jne 260b
	sub ebp, 256
	mov eax, DWORD PTR [ebp+1360]
	add eax, ebx
	mov DWORD PTR [ebp+1360], eax
	mov eax, DWORD PTR [ebp+1364]
	adc eax, 0
	mov DWORD PTR [ebp+1364], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 258b
	mov ecx, 0
	mov ebp, edi
261:
	mov eax, DWORD PTR [ebp+1360]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+584], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 261b
	mov eax, DWORD PTR [edi+1616]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
262:
	mov eax, DWORD PTR [ebp+1360]
	mov edx, DWORD PTR [ebp+584]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+3184], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 262b
	mov ebx, 0
	mov eax, DWORD PTR [edi+4224]
	shr eax, 31
	and eax, 1
	or ebx, eax
	mov eax, DWORD PTR [edi+4228]
	shr eax, 31
	and eax, 1
	add eax, eax
	or ebx, eax
	mov eax, DWORD PTR [edi+4232]
	shr eax, 31
	and eax, 1
	add eax, eax
	add eax, eax
	or ebx, eax
	mov eax, DWORD PTR [edi+4236]
	shr eax, 31
	and eax, 1
	add eax, eax
	add eax, eax
	add eax, eax
	or ebx, eax
	mov eax, DWORD PTR [edi+4240]
	shr eax, 31
	and eax, 1
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	or ebx, eax
	mov DWORD PTR [edi+4], ebx
	mov ecx, 0
	mov ebp, edi
263:
	mov eax, DWORD PTR [ebp+4224]
	mov ebx, eax
	shr ebx, 31
	add eax, eax
	add eax, ecx
	mov DWORD PTR [ebp+4224], eax
	mov ecx, ebx
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 263b
	mov eax, DWORD PTR [edi+4]
	mov edx, 256
	mul edx
	add eax, edi
	add eax, 16896
	mov ecx, eax
	mov ebp, edi
	mov ebx, 64
264:
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [ebp+3704], eax
	add ecx, 4
	add ebp, 4
	sub ebx, 1
	jne 264b
	mov eax, 0
	mov ebp, edi
265:
	mov DWORD PTR [ebp+1104], eax
	add ebp, 4
	mov edx, edi
	add edx, 516
	cmp ebp, edx
	jne 265b
	mov ebp, edi
266:
	mov eax, DWORD PTR [ebp+3184]
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
267:
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+3704]
	mul edx
	add eax, DWORD PTR [ebp+1104]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+3708]
	mul edx
	add eax, DWORD PTR [ebp+1108]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1108], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 256
	cmp ecx, eax
	jne 267b
	sub ebp, 256
	mov eax, DWORD PTR [ebp+1360]
	add eax, ebx
	mov DWORD PTR [ebp+1360], eax
	mov eax, DWORD PTR [ebp+1364]
	adc eax, 0
	mov DWORD PTR [ebp+1364], eax
	mov eax, DWORD PTR [ebp+1104]
	mov edx, DWORD PTR [edi]
	mul edx
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
268:
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	add eax, DWORD PTR [ebp+1104]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	add eax, DWORD PTR [ebp+1108]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1108], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 256
	cmp ecx, eax
	jne 268b
	sub ebp, 256
	mov eax, DWORD PTR [ebp+1360]
	add eax, ebx
	mov DWORD PTR [ebp+1360], eax
	mov eax, DWORD PTR [ebp+1364]
	adc eax, 0
	mov DWORD PTR [ebp+1364], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 266b
	mov ecx, 0
	mov ebp, edi
269:
	mov eax, DWORD PTR [ebp+1360]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+584], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 269b
	mov eax, DWORD PTR [edi+1616]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
270:
	mov eax, DWORD PTR [ebp+1360]
	mov edx, DWORD PTR [ebp+584]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+3184], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 270b
	sub esi, 1
	cmp esi, 0
	jne 256b
	mov eax, 0
	mov ebp, edi
271:
	mov DWORD PTR [ebp+1104], eax
	add ebp, 4
	mov edx, edi
	add edx, 516
	cmp ebp, edx
	jne 271b
	mov ebp, edi
272:
	mov eax, DWORD PTR [ebp+3184]
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
273:
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+1624]
	mul edx
	add eax, DWORD PTR [ebp+1104]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+1628]
	mul edx
	add eax, DWORD PTR [ebp+1108]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1108], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 256
	cmp ecx, eax
	jne 273b
	sub ebp, 256
	mov eax, DWORD PTR [ebp+1360]
	add eax, ebx
	mov DWORD PTR [ebp+1360], eax
	mov eax, DWORD PTR [ebp+1364]
	adc eax, 0
	mov DWORD PTR [ebp+1364], eax
	mov eax, DWORD PTR [ebp+1104]
	mov edx, DWORD PTR [edi]
	mul edx
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
274:
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	add eax, DWORD PTR [ebp+1104]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	add eax, DWORD PTR [ebp+1108]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1108], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 256
	cmp ecx, eax
	jne 274b
	sub ebp, 256
	mov eax, DWORD PTR [ebp+1360]
	add eax, ebx
	mov DWORD PTR [ebp+1360], eax
	mov eax, DWORD PTR [ebp+1364]
	adc eax, 0
	mov DWORD PTR [ebp+1364], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 272b
	mov ecx, 0
	mov ebp, edi
275:
	mov eax, DWORD PTR [ebp+1360]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+584], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 275b
	mov eax, DWORD PTR [edi+1616]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
276:
	mov eax, DWORD PTR [ebp+1360]
	mov edx, DWORD PTR [ebp+584]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+3184], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 276b
	mov ebx, DWORD PTR [edi+8]
	mov esi, DWORD PTR [edi+12]
	mov ebp, DWORD PTR [edi+16]
	mov edi, DWORD PTR [edi+20]
	ret
	.p2align 6
