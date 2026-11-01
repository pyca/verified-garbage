// The functions of `src/internal/vg_dsa_comb_pow_32_5.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_comb_pow_32_5:
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
	mov ecx, 0
	mov ebp, edi
21:
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
	jne 21b
	mov esi, 32
22:
	mov eax, 0
	mov ebp, edi
23:
	mov DWORD PTR [ebp+1104], eax
	add ebp, 4
	mov edx, edi
	add edx, 516
	cmp ebp, edx
	jne 23b
	mov ebp, edi
24:
	mov eax, DWORD PTR [ebp+3184]
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
25:
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
	jne 25b
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
26:
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
	jne 26b
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
	jne 24b
	mov ecx, 0
	mov ebp, edi
27:
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
	jne 27b
	mov eax, DWORD PTR [edi+1616]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
28:
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
	jne 28b
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
29:
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
	jne 29b
	mov eax, DWORD PTR [edi+4]
	xor eax, 0
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+584], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 1
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+588], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 2
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+592], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 3
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+596], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 4
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+600], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 5
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+604], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 6
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+608], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 7
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+612], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 8
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+616], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 9
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+620], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 10
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+624], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 11
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+628], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 12
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+632], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 13
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+636], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 14
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+640], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 15
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+644], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 16
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+648], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 17
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+652], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 18
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+656], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 19
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+660], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 20
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+664], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 21
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+668], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 22
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+672], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 23
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+676], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 24
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+680], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 25
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+684], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 26
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+688], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 27
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+692], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 28
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+696], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 29
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+700], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 30
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+704], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 31
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+708], ecx
	mov ebp, edi
210:
	mov ebx, 0
	mov eax, DWORD PTR [ebp+16896]
	and eax, DWORD PTR [edi+584]
	or ebx, eax
	mov eax, DWORD PTR [ebp+17152]
	and eax, DWORD PTR [edi+588]
	or ebx, eax
	mov eax, DWORD PTR [ebp+17408]
	and eax, DWORD PTR [edi+592]
	or ebx, eax
	mov eax, DWORD PTR [ebp+17664]
	and eax, DWORD PTR [edi+596]
	or ebx, eax
	mov eax, DWORD PTR [ebp+17920]
	and eax, DWORD PTR [edi+600]
	or ebx, eax
	mov eax, DWORD PTR [ebp+18176]
	and eax, DWORD PTR [edi+604]
	or ebx, eax
	mov eax, DWORD PTR [ebp+18432]
	and eax, DWORD PTR [edi+608]
	or ebx, eax
	mov eax, DWORD PTR [ebp+18688]
	and eax, DWORD PTR [edi+612]
	or ebx, eax
	mov eax, DWORD PTR [ebp+18944]
	and eax, DWORD PTR [edi+616]
	or ebx, eax
	mov eax, DWORD PTR [ebp+19200]
	and eax, DWORD PTR [edi+620]
	or ebx, eax
	mov eax, DWORD PTR [ebp+19456]
	and eax, DWORD PTR [edi+624]
	or ebx, eax
	mov eax, DWORD PTR [ebp+19712]
	and eax, DWORD PTR [edi+628]
	or ebx, eax
	mov eax, DWORD PTR [ebp+19968]
	and eax, DWORD PTR [edi+632]
	or ebx, eax
	mov eax, DWORD PTR [ebp+20224]
	and eax, DWORD PTR [edi+636]
	or ebx, eax
	mov eax, DWORD PTR [ebp+20480]
	and eax, DWORD PTR [edi+640]
	or ebx, eax
	mov eax, DWORD PTR [ebp+20736]
	and eax, DWORD PTR [edi+644]
	or ebx, eax
	mov eax, DWORD PTR [ebp+20992]
	and eax, DWORD PTR [edi+648]
	or ebx, eax
	mov eax, DWORD PTR [ebp+21248]
	and eax, DWORD PTR [edi+652]
	or ebx, eax
	mov eax, DWORD PTR [ebp+21504]
	and eax, DWORD PTR [edi+656]
	or ebx, eax
	mov eax, DWORD PTR [ebp+21760]
	and eax, DWORD PTR [edi+660]
	or ebx, eax
	mov eax, DWORD PTR [ebp+22016]
	and eax, DWORD PTR [edi+664]
	or ebx, eax
	mov eax, DWORD PTR [ebp+22272]
	and eax, DWORD PTR [edi+668]
	or ebx, eax
	mov eax, DWORD PTR [ebp+22528]
	and eax, DWORD PTR [edi+672]
	or ebx, eax
	mov eax, DWORD PTR [ebp+22784]
	and eax, DWORD PTR [edi+676]
	or ebx, eax
	mov eax, DWORD PTR [ebp+23040]
	and eax, DWORD PTR [edi+680]
	or ebx, eax
	mov eax, DWORD PTR [ebp+23296]
	and eax, DWORD PTR [edi+684]
	or ebx, eax
	mov eax, DWORD PTR [ebp+23552]
	and eax, DWORD PTR [edi+688]
	or ebx, eax
	mov eax, DWORD PTR [ebp+23808]
	and eax, DWORD PTR [edi+692]
	or ebx, eax
	mov eax, DWORD PTR [ebp+24064]
	and eax, DWORD PTR [edi+696]
	or ebx, eax
	mov eax, DWORD PTR [ebp+24320]
	and eax, DWORD PTR [edi+700]
	or ebx, eax
	mov eax, DWORD PTR [ebp+24576]
	and eax, DWORD PTR [edi+704]
	or ebx, eax
	mov eax, DWORD PTR [ebp+24832]
	and eax, DWORD PTR [edi+708]
	or ebx, eax
	mov DWORD PTR [ebp+3704], ebx
	add ebp, 4
	mov eax, edi
	add eax, 256
	cmp ebp, eax
	jne 210b
	mov eax, 0
	mov ebp, edi
211:
	mov DWORD PTR [ebp+1104], eax
	add ebp, 4
	mov edx, edi
	add edx, 516
	cmp ebp, edx
	jne 211b
	mov ebp, edi
212:
	mov eax, DWORD PTR [ebp+3184]
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
213:
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
	jne 213b
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
214:
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
	jne 214b
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
	jne 212b
	mov ecx, 0
	mov ebp, edi
215:
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
	jne 215b
	mov eax, DWORD PTR [edi+1616]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
216:
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
	jne 216b
	sub esi, 1
	cmp esi, 0
	jne 22b
	mov eax, 0
	mov ebp, edi
217:
	mov DWORD PTR [ebp+1104], eax
	add ebp, 4
	mov edx, edi
	add edx, 516
	cmp ebp, edx
	jne 217b
	mov ebp, edi
218:
	mov eax, DWORD PTR [ebp+3184]
	mov DWORD PTR [edi+584], eax
	mov ebx, 0
	mov ecx, edi
219:
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
	jne 219b
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
220:
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
	jne 220b
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
	jne 218b
	mov ecx, 0
	mov ebp, edi
221:
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
	jne 221b
	mov eax, DWORD PTR [edi+1616]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
222:
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
	jne 222b
	mov ebx, DWORD PTR [edi+8]
	mov esi, DWORD PTR [edi+12]
	mov ebp, DWORD PTR [edi+16]
	mov edi, DWORD PTR [edi+20]
	ret
	.p2align 6
