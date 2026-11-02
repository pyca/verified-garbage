// The functions of `src/internal/vg_dsa_comb_pow_16_5.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_comb_pow_16_5:
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
	mov DWORD PTR [ebp+856], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 20b
	mov eax, 1
	mov DWORD PTR [edi+856], eax
	mov ecx, 0
	mov ebp, edi
21:
	mov eax, DWORD PTR [ebp+9472]
	mov edx, DWORD PTR [ebp+9472]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+1648], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 21b
	mov esi, 32
22:
	mov eax, 0
	mov ebp, edi
23:
	mov DWORD PTR [ebp+592], eax
	add ebp, 4
	mov edx, edi
	add edx, 260
	cmp ebp, edx
	jne 23b
	mov ebp, edi
24:
	mov eax, DWORD PTR [ebp+1648]
	mov DWORD PTR [edi+328], eax
	mov ebx, 0
	mov ecx, edi
25:
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [ecx+1648]
	mul edx
	add eax, DWORD PTR [ebp+592]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+592], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [ecx+1652]
	mul edx
	add eax, DWORD PTR [ebp+596]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+596], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 128
	cmp ecx, eax
	jne 25b
	sub ebp, 128
	mov eax, DWORD PTR [ebp+720]
	add eax, ebx
	mov DWORD PTR [ebp+720], eax
	mov eax, DWORD PTR [ebp+724]
	adc eax, 0
	mov DWORD PTR [ebp+724], eax
	mov eax, DWORD PTR [ebp+592]
	mov edx, DWORD PTR [edi]
	mul edx
	mov DWORD PTR [edi+328], eax
	mov ebx, 0
	mov ecx, edi
26:
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	add eax, DWORD PTR [ebp+592]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+592], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	add eax, DWORD PTR [ebp+596]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+596], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 128
	cmp ecx, eax
	jne 26b
	sub ebp, 128
	mov eax, DWORD PTR [ebp+720]
	add eax, ebx
	mov DWORD PTR [ebp+720], eax
	mov eax, DWORD PTR [ebp+724]
	adc eax, 0
	mov DWORD PTR [ebp+724], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 24b
	mov ecx, 0
	mov ebp, edi
27:
	mov eax, DWORD PTR [ebp+720]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+328], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 27b
	mov eax, DWORD PTR [edi+848]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
28:
	mov eax, DWORD PTR [ebp+720]
	mov edx, DWORD PTR [ebp+328]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+1648], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 28b
	mov ebx, 0
	mov eax, DWORD PTR [edi+2176]
	shr eax, 31
	and eax, 1
	or ebx, eax
	mov eax, DWORD PTR [edi+2180]
	shr eax, 31
	and eax, 1
	add eax, eax
	or ebx, eax
	mov eax, DWORD PTR [edi+2184]
	shr eax, 31
	and eax, 1
	add eax, eax
	add eax, eax
	or ebx, eax
	mov eax, DWORD PTR [edi+2188]
	shr eax, 31
	and eax, 1
	add eax, eax
	add eax, eax
	add eax, eax
	or ebx, eax
	mov eax, DWORD PTR [edi+2192]
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
29:
	mov eax, DWORD PTR [ebp+2176]
	mov ebx, eax
	shr ebx, 31
	add eax, eax
	add eax, ecx
	mov DWORD PTR [ebp+2176], eax
	mov ecx, ebx
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 29b
	mov eax, DWORD PTR [edi+4]
	xor eax, 0
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+328], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 1
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+332], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 2
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+336], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 3
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+340], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 4
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+344], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 5
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+348], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 6
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+352], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 7
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+356], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 8
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+360], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 9
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+364], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 10
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+368], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 11
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+372], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 12
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+376], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 13
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+380], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 14
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+384], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 15
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+388], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 16
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+392], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 17
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+396], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 18
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+400], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 19
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+404], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 20
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+408], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 21
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+412], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 22
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+416], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 23
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+420], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 24
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+424], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 25
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+428], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 26
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+432], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 27
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+436], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 28
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+440], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 29
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+444], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 30
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+448], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 31
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+452], ecx
	mov ebp, edi
210:
	mov ebx, 0
	mov eax, DWORD PTR [ebp+9472]
	and eax, DWORD PTR [edi+328]
	or ebx, eax
	mov eax, DWORD PTR [ebp+9600]
	and eax, DWORD PTR [edi+332]
	or ebx, eax
	mov eax, DWORD PTR [ebp+9728]
	and eax, DWORD PTR [edi+336]
	or ebx, eax
	mov eax, DWORD PTR [ebp+9856]
	and eax, DWORD PTR [edi+340]
	or ebx, eax
	mov eax, DWORD PTR [ebp+9984]
	and eax, DWORD PTR [edi+344]
	or ebx, eax
	mov eax, DWORD PTR [ebp+10112]
	and eax, DWORD PTR [edi+348]
	or ebx, eax
	mov eax, DWORD PTR [ebp+10240]
	and eax, DWORD PTR [edi+352]
	or ebx, eax
	mov eax, DWORD PTR [ebp+10368]
	and eax, DWORD PTR [edi+356]
	or ebx, eax
	mov eax, DWORD PTR [ebp+10496]
	and eax, DWORD PTR [edi+360]
	or ebx, eax
	mov eax, DWORD PTR [ebp+10624]
	and eax, DWORD PTR [edi+364]
	or ebx, eax
	mov eax, DWORD PTR [ebp+10752]
	and eax, DWORD PTR [edi+368]
	or ebx, eax
	mov eax, DWORD PTR [ebp+10880]
	and eax, DWORD PTR [edi+372]
	or ebx, eax
	mov eax, DWORD PTR [ebp+11008]
	and eax, DWORD PTR [edi+376]
	or ebx, eax
	mov eax, DWORD PTR [ebp+11136]
	and eax, DWORD PTR [edi+380]
	or ebx, eax
	mov eax, DWORD PTR [ebp+11264]
	and eax, DWORD PTR [edi+384]
	or ebx, eax
	mov eax, DWORD PTR [ebp+11392]
	and eax, DWORD PTR [edi+388]
	or ebx, eax
	mov eax, DWORD PTR [ebp+11520]
	and eax, DWORD PTR [edi+392]
	or ebx, eax
	mov eax, DWORD PTR [ebp+11648]
	and eax, DWORD PTR [edi+396]
	or ebx, eax
	mov eax, DWORD PTR [ebp+11776]
	and eax, DWORD PTR [edi+400]
	or ebx, eax
	mov eax, DWORD PTR [ebp+11904]
	and eax, DWORD PTR [edi+404]
	or ebx, eax
	mov eax, DWORD PTR [ebp+12032]
	and eax, DWORD PTR [edi+408]
	or ebx, eax
	mov eax, DWORD PTR [ebp+12160]
	and eax, DWORD PTR [edi+412]
	or ebx, eax
	mov eax, DWORD PTR [ebp+12288]
	and eax, DWORD PTR [edi+416]
	or ebx, eax
	mov eax, DWORD PTR [ebp+12416]
	and eax, DWORD PTR [edi+420]
	or ebx, eax
	mov eax, DWORD PTR [ebp+12544]
	and eax, DWORD PTR [edi+424]
	or ebx, eax
	mov eax, DWORD PTR [ebp+12672]
	and eax, DWORD PTR [edi+428]
	or ebx, eax
	mov eax, DWORD PTR [ebp+12800]
	and eax, DWORD PTR [edi+432]
	or ebx, eax
	mov eax, DWORD PTR [ebp+12928]
	and eax, DWORD PTR [edi+436]
	or ebx, eax
	mov eax, DWORD PTR [ebp+13056]
	and eax, DWORD PTR [edi+440]
	or ebx, eax
	mov eax, DWORD PTR [ebp+13184]
	and eax, DWORD PTR [edi+444]
	or ebx, eax
	mov eax, DWORD PTR [ebp+13312]
	and eax, DWORD PTR [edi+448]
	or ebx, eax
	mov eax, DWORD PTR [ebp+13440]
	and eax, DWORD PTR [edi+452]
	or ebx, eax
	mov DWORD PTR [ebp+1912], ebx
	add ebp, 4
	mov eax, edi
	add eax, 128
	cmp ebp, eax
	jne 210b
	mov eax, 0
	mov ebp, edi
211:
	mov DWORD PTR [ebp+592], eax
	add ebp, 4
	mov edx, edi
	add edx, 260
	cmp ebp, edx
	jne 211b
	mov ebp, edi
212:
	mov eax, DWORD PTR [ebp+1648]
	mov DWORD PTR [edi+328], eax
	mov ebx, 0
	mov ecx, edi
213:
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [ecx+1912]
	mul edx
	add eax, DWORD PTR [ebp+592]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+592], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [ecx+1916]
	mul edx
	add eax, DWORD PTR [ebp+596]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+596], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 128
	cmp ecx, eax
	jne 213b
	sub ebp, 128
	mov eax, DWORD PTR [ebp+720]
	add eax, ebx
	mov DWORD PTR [ebp+720], eax
	mov eax, DWORD PTR [ebp+724]
	adc eax, 0
	mov DWORD PTR [ebp+724], eax
	mov eax, DWORD PTR [ebp+592]
	mov edx, DWORD PTR [edi]
	mul edx
	mov DWORD PTR [edi+328], eax
	mov ebx, 0
	mov ecx, edi
214:
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	add eax, DWORD PTR [ebp+592]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+592], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	add eax, DWORD PTR [ebp+596]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+596], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 128
	cmp ecx, eax
	jne 214b
	sub ebp, 128
	mov eax, DWORD PTR [ebp+720]
	add eax, ebx
	mov DWORD PTR [ebp+720], eax
	mov eax, DWORD PTR [ebp+724]
	adc eax, 0
	mov DWORD PTR [ebp+724], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 212b
	mov ecx, 0
	mov ebp, edi
215:
	mov eax, DWORD PTR [ebp+720]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+328], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 215b
	mov eax, DWORD PTR [edi+848]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
216:
	mov eax, DWORD PTR [ebp+720]
	mov edx, DWORD PTR [ebp+328]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+1648], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 216b
	sub esi, 1
	cmp esi, 0
	jne 22b
	mov eax, 0
	mov ebp, edi
217:
	mov DWORD PTR [ebp+592], eax
	add ebp, 4
	mov edx, edi
	add edx, 260
	cmp ebp, edx
	jne 217b
	mov ebp, edi
218:
	mov eax, DWORD PTR [ebp+1648]
	mov DWORD PTR [edi+328], eax
	mov ebx, 0
	mov ecx, edi
219:
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [ecx+856]
	mul edx
	add eax, DWORD PTR [ebp+592]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+592], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [ecx+860]
	mul edx
	add eax, DWORD PTR [ebp+596]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+596], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 128
	cmp ecx, eax
	jne 219b
	sub ebp, 128
	mov eax, DWORD PTR [ebp+720]
	add eax, ebx
	mov DWORD PTR [ebp+720], eax
	mov eax, DWORD PTR [ebp+724]
	adc eax, 0
	mov DWORD PTR [ebp+724], eax
	mov eax, DWORD PTR [ebp+592]
	mov edx, DWORD PTR [edi]
	mul edx
	mov DWORD PTR [edi+328], eax
	mov ebx, 0
	mov ecx, edi
220:
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	add eax, DWORD PTR [ebp+592]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+592], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	add eax, DWORD PTR [ebp+596]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+596], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 128
	cmp ecx, eax
	jne 220b
	sub ebp, 128
	mov eax, DWORD PTR [ebp+720]
	add eax, ebx
	mov DWORD PTR [ebp+720], eax
	mov eax, DWORD PTR [ebp+724]
	adc eax, 0
	mov DWORD PTR [ebp+724], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 218b
	mov ecx, 0
	mov ebp, edi
221:
	mov eax, DWORD PTR [ebp+720]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+328], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 221b
	mov eax, DWORD PTR [edi+848]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
222:
	mov eax, DWORD PTR [ebp+720]
	mov edx, DWORD PTR [ebp+328]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+1648], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 222b
	mov ebx, DWORD PTR [edi+8]
	mov esi, DWORD PTR [edi+12]
	mov ebp, DWORD PTR [edi+16]
	mov edi, DWORD PTR [edi+20]
	ret
	.p2align 6
