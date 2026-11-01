// The functions of `src/internal/vg_dsa_comb_pow_48_8.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_comb_pow_48_8:
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
	mov DWORD PTR [ebp+2392], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 20b
	mov eax, 1
	mov DWORD PTR [edi+2392], eax
	mov ecx, 0
	mov ebp, edi
21:
	mov eax, DWORD PTR [ebp+17152]
	mov edx, DWORD PTR [ebp+17152]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+4720], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 21b
	mov eax, 0
	mov ebp, edi
22:
	mov DWORD PTR [ebp+6304], eax
	add ebp, 4
	mov edx, edi
	add edx, 4
	cmp ebp, edx
	jne 22b
	mov esi, 52
23:
	mov eax, 0
	mov ebp, edi
24:
	mov DWORD PTR [ebp+1616], eax
	add ebp, 4
	mov edx, edi
	add edx, 772
	cmp ebp, edx
	jne 24b
	mov ebp, edi
25:
	mov eax, DWORD PTR [ebp+4720]
	mov DWORD PTR [edi+840], eax
	mov ebx, 0
	mov ecx, edi
26:
	mov eax, DWORD PTR [edi+840]
	mov edx, DWORD PTR [ecx+4720]
	mul edx
	add eax, DWORD PTR [ebp+1616]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1616], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+840]
	mov edx, DWORD PTR [ecx+4724]
	mul edx
	add eax, DWORD PTR [ebp+1620]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1620], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 384
	cmp ecx, eax
	jne 26b
	sub ebp, 384
	mov eax, DWORD PTR [ebp+2000]
	add eax, ebx
	mov DWORD PTR [ebp+2000], eax
	mov eax, DWORD PTR [ebp+2004]
	adc eax, 0
	mov DWORD PTR [ebp+2004], eax
	mov eax, DWORD PTR [ebp+1616]
	mov edx, DWORD PTR [edi]
	mul edx
	mov DWORD PTR [edi+840], eax
	mov ebx, 0
	mov ecx, edi
27:
	mov eax, DWORD PTR [edi+840]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	add eax, DWORD PTR [ebp+1616]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1616], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+840]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	add eax, DWORD PTR [ebp+1620]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1620], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 384
	cmp ecx, eax
	jne 27b
	sub ebp, 384
	mov eax, DWORD PTR [ebp+2000]
	add eax, ebx
	mov DWORD PTR [ebp+2000], eax
	mov eax, DWORD PTR [ebp+2004]
	adc eax, 0
	mov DWORD PTR [ebp+2004], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 25b
	mov ecx, 0
	mov ebp, edi
28:
	mov eax, DWORD PTR [ebp+2000]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+840], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 28b
	mov eax, DWORD PTR [edi+2384]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
29:
	mov eax, DWORD PTR [ebp+2000]
	mov edx, DWORD PTR [ebp+840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+4720], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 29b
	mov ebx, 0
	mov eax, DWORD PTR [edi+6276]
	shr eax, 19
	and eax, 1
	or ebx, eax
	mov eax, DWORD PTR [edi+6284]
	shr eax, 7
	and eax, 1
	add eax, eax
	or ebx, eax
	mov eax, DWORD PTR [edi+6288]
	shr eax, 27
	and eax, 1
	add eax, eax
	add eax, eax
	or ebx, eax
	mov eax, DWORD PTR [edi+6296]
	shr eax, 15
	and eax, 1
	add eax, eax
	add eax, eax
	add eax, eax
	or ebx, eax
	mov eax, DWORD PTR [edi+6304]
	shr eax, 3
	and eax, 1
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	or ebx, eax
	mov DWORD PTR [edi+4], ebx
	mov ecx, 0
	mov ebp, edi
210:
	mov eax, DWORD PTR [ebp+6272]
	mov ebx, eax
	shr ebx, 31
	add eax, eax
	add eax, ecx
	mov DWORD PTR [ebp+6272], eax
	mov ecx, ebx
	add ebp, 4
	mov edx, edi
	add edx, 36
	cmp ebp, edx
	jne 210b
	mov eax, DWORD PTR [edi+4]
	xor eax, 0
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+840], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 1
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+844], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 2
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+848], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 3
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+852], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 4
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+856], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 5
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+860], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 6
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+864], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 7
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+868], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 8
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+872], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 9
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+876], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 10
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+880], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 11
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+884], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 12
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+888], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 13
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+892], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 14
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+896], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 15
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+900], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 16
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+904], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 17
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+908], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 18
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+912], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 19
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+916], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 20
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+920], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 21
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+924], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 22
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+928], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 23
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+932], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 24
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+936], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 25
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+940], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 26
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+944], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 27
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+948], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 28
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+952], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 29
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+956], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 30
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+960], ecx
	mov eax, DWORD PTR [edi+4]
	xor eax, 31
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+964], ecx
	mov ebp, edi
211:
	mov ebx, 0
	mov eax, DWORD PTR [ebp+17152]
	and eax, DWORD PTR [edi+840]
	or ebx, eax
	mov eax, DWORD PTR [ebp+17536]
	and eax, DWORD PTR [edi+844]
	or ebx, eax
	mov eax, DWORD PTR [ebp+17920]
	and eax, DWORD PTR [edi+848]
	or ebx, eax
	mov eax, DWORD PTR [ebp+18304]
	and eax, DWORD PTR [edi+852]
	or ebx, eax
	mov eax, DWORD PTR [ebp+18688]
	and eax, DWORD PTR [edi+856]
	or ebx, eax
	mov eax, DWORD PTR [ebp+19072]
	and eax, DWORD PTR [edi+860]
	or ebx, eax
	mov eax, DWORD PTR [ebp+19456]
	and eax, DWORD PTR [edi+864]
	or ebx, eax
	mov eax, DWORD PTR [ebp+19840]
	and eax, DWORD PTR [edi+868]
	or ebx, eax
	mov eax, DWORD PTR [ebp+20224]
	and eax, DWORD PTR [edi+872]
	or ebx, eax
	mov eax, DWORD PTR [ebp+20608]
	and eax, DWORD PTR [edi+876]
	or ebx, eax
	mov eax, DWORD PTR [ebp+20992]
	and eax, DWORD PTR [edi+880]
	or ebx, eax
	mov eax, DWORD PTR [ebp+21376]
	and eax, DWORD PTR [edi+884]
	or ebx, eax
	mov eax, DWORD PTR [ebp+21760]
	and eax, DWORD PTR [edi+888]
	or ebx, eax
	mov eax, DWORD PTR [ebp+22144]
	and eax, DWORD PTR [edi+892]
	or ebx, eax
	mov eax, DWORD PTR [ebp+22528]
	and eax, DWORD PTR [edi+896]
	or ebx, eax
	mov eax, DWORD PTR [ebp+22912]
	and eax, DWORD PTR [edi+900]
	or ebx, eax
	mov eax, DWORD PTR [ebp+23296]
	and eax, DWORD PTR [edi+904]
	or ebx, eax
	mov eax, DWORD PTR [ebp+23680]
	and eax, DWORD PTR [edi+908]
	or ebx, eax
	mov eax, DWORD PTR [ebp+24064]
	and eax, DWORD PTR [edi+912]
	or ebx, eax
	mov eax, DWORD PTR [ebp+24448]
	and eax, DWORD PTR [edi+916]
	or ebx, eax
	mov eax, DWORD PTR [ebp+24832]
	and eax, DWORD PTR [edi+920]
	or ebx, eax
	mov eax, DWORD PTR [ebp+25216]
	and eax, DWORD PTR [edi+924]
	or ebx, eax
	mov eax, DWORD PTR [ebp+25600]
	and eax, DWORD PTR [edi+928]
	or ebx, eax
	mov eax, DWORD PTR [ebp+25984]
	and eax, DWORD PTR [edi+932]
	or ebx, eax
	mov eax, DWORD PTR [ebp+26368]
	and eax, DWORD PTR [edi+936]
	or ebx, eax
	mov eax, DWORD PTR [ebp+26752]
	and eax, DWORD PTR [edi+940]
	or ebx, eax
	mov eax, DWORD PTR [ebp+27136]
	and eax, DWORD PTR [edi+944]
	or ebx, eax
	mov eax, DWORD PTR [ebp+27520]
	and eax, DWORD PTR [edi+948]
	or ebx, eax
	mov eax, DWORD PTR [ebp+27904]
	and eax, DWORD PTR [edi+952]
	or ebx, eax
	mov eax, DWORD PTR [ebp+28288]
	and eax, DWORD PTR [edi+956]
	or ebx, eax
	mov eax, DWORD PTR [ebp+28672]
	and eax, DWORD PTR [edi+960]
	or ebx, eax
	mov eax, DWORD PTR [ebp+29056]
	and eax, DWORD PTR [edi+964]
	or ebx, eax
	mov DWORD PTR [ebp+5496], ebx
	add ebp, 4
	mov eax, edi
	add eax, 384
	cmp ebp, eax
	jne 211b
	mov eax, 0
	mov ebp, edi
212:
	mov DWORD PTR [ebp+1616], eax
	add ebp, 4
	mov edx, edi
	add edx, 772
	cmp ebp, edx
	jne 212b
	mov ebp, edi
213:
	mov eax, DWORD PTR [ebp+4720]
	mov DWORD PTR [edi+840], eax
	mov ebx, 0
	mov ecx, edi
214:
	mov eax, DWORD PTR [edi+840]
	mov edx, DWORD PTR [ecx+5496]
	mul edx
	add eax, DWORD PTR [ebp+1616]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1616], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+840]
	mov edx, DWORD PTR [ecx+5500]
	mul edx
	add eax, DWORD PTR [ebp+1620]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1620], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 384
	cmp ecx, eax
	jne 214b
	sub ebp, 384
	mov eax, DWORD PTR [ebp+2000]
	add eax, ebx
	mov DWORD PTR [ebp+2000], eax
	mov eax, DWORD PTR [ebp+2004]
	adc eax, 0
	mov DWORD PTR [ebp+2004], eax
	mov eax, DWORD PTR [ebp+1616]
	mov edx, DWORD PTR [edi]
	mul edx
	mov DWORD PTR [edi+840], eax
	mov ebx, 0
	mov ecx, edi
215:
	mov eax, DWORD PTR [edi+840]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	add eax, DWORD PTR [ebp+1616]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1616], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+840]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	add eax, DWORD PTR [ebp+1620]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1620], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 384
	cmp ecx, eax
	jne 215b
	sub ebp, 384
	mov eax, DWORD PTR [ebp+2000]
	add eax, ebx
	mov DWORD PTR [ebp+2000], eax
	mov eax, DWORD PTR [ebp+2004]
	adc eax, 0
	mov DWORD PTR [ebp+2004], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 213b
	mov ecx, 0
	mov ebp, edi
216:
	mov eax, DWORD PTR [ebp+2000]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+840], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 216b
	mov eax, DWORD PTR [edi+2384]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
217:
	mov eax, DWORD PTR [ebp+2000]
	mov edx, DWORD PTR [ebp+840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+4720], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 217b
	sub esi, 1
	cmp esi, 0
	jne 23b
	mov eax, 0
	mov ebp, edi
218:
	mov DWORD PTR [ebp+1616], eax
	add ebp, 4
	mov edx, edi
	add edx, 772
	cmp ebp, edx
	jne 218b
	mov ebp, edi
219:
	mov eax, DWORD PTR [ebp+4720]
	mov DWORD PTR [edi+840], eax
	mov ebx, 0
	mov ecx, edi
220:
	mov eax, DWORD PTR [edi+840]
	mov edx, DWORD PTR [ecx+2392]
	mul edx
	add eax, DWORD PTR [ebp+1616]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1616], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+840]
	mov edx, DWORD PTR [ecx+2396]
	mul edx
	add eax, DWORD PTR [ebp+1620]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1620], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 384
	cmp ecx, eax
	jne 220b
	sub ebp, 384
	mov eax, DWORD PTR [ebp+2000]
	add eax, ebx
	mov DWORD PTR [ebp+2000], eax
	mov eax, DWORD PTR [ebp+2004]
	adc eax, 0
	mov DWORD PTR [ebp+2004], eax
	mov eax, DWORD PTR [ebp+1616]
	mov edx, DWORD PTR [edi]
	mul edx
	mov DWORD PTR [edi+840], eax
	mov ebx, 0
	mov ecx, edi
221:
	mov eax, DWORD PTR [edi+840]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	add eax, DWORD PTR [ebp+1616]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1616], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+840]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	add eax, DWORD PTR [ebp+1620]
	adc edx, 0
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+1620], eax
	mov ebx, edx
	add ecx, 8
	add ebp, 8
	mov eax, edi
	add eax, 384
	cmp ecx, eax
	jne 221b
	sub ebp, 384
	mov eax, DWORD PTR [ebp+2000]
	add eax, ebx
	mov DWORD PTR [ebp+2000], eax
	mov eax, DWORD PTR [ebp+2004]
	adc eax, 0
	mov DWORD PTR [ebp+2004], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 219b
	mov ecx, 0
	mov ebp, edi
222:
	mov eax, DWORD PTR [ebp+2000]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+840], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 222b
	mov eax, DWORD PTR [edi+2384]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
223:
	mov eax, DWORD PTR [ebp+2000]
	mov edx, DWORD PTR [ebp+840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+4720], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 223b
	mov ebx, DWORD PTR [edi+8]
	mov esi, DWORD PTR [edi+12]
	mov ebp, DWORD PTR [edi+16]
	mov edi, DWORD PTR [edi+20]
	ret
	.p2align 6
