// The functions of `src/internal/vg_dsa_pow_48_8.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_pow_48_8:
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
	mov eax, DWORD PTR [edi+444]
	shr eax, 31
	cmp eax, 1
	je 21f
	mov eax, 0
	mov ebp, edi
23:
	mov DWORD PTR [ebp+3168], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 23b
	mov eax, 1
	mov DWORD PTR [edi+3168], eax
	mov esi, 3120
24:
	mov ecx, 0
	mov ebp, edi
25:
	mov eax, DWORD PTR [ebp+3168]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+3168]
	mov DWORD PTR [ebp+1616], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 25b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+2000], eax
	mov ecx, 0
	mov ebp, edi
26:
	mov eax, DWORD PTR [ebp+1616]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+840], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 26b
	mov eax, DWORD PTR [edi+2000]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
27:
	mov eax, DWORD PTR [ebp+1616]
	mov edx, DWORD PTR [ebp+840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+3168], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
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
	mov DWORD PTR [ebp+3168], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 28b
	mov eax, -2147483648
	mov DWORD PTR [edi+3548], eax
	mov esi, 49
29:
	mov ecx, 0
	mov ebp, edi
210:
	mov eax, DWORD PTR [ebp+3168]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+3168]
	mov DWORD PTR [ebp+1616], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 210b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+2000], eax
	mov ecx, 0
	mov ebp, edi
211:
	mov eax, DWORD PTR [ebp+1616]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+840], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 211b
	mov eax, DWORD PTR [edi+2000]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
212:
	mov eax, DWORD PTR [ebp+1616]
	mov edx, DWORD PTR [ebp+840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+3168], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 212b
	sub esi, 1
	cmp esi, 0
	jne 29b
22:
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 881
	mov DWORD PTR [esp+4], eax
	mov eax, 48
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 840
	mov DWORD PTR [esp+20], eax
	mov eax, 3168
	mov DWORD PTR [esp+24], eax
	mov eax, 3168
	mov DWORD PTR [esp+28], eax
	mov eax, 3168
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 881
	mov DWORD PTR [esp+4], eax
	mov eax, 48
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 840
	mov DWORD PTR [esp+20], eax
	mov eax, 3168
	mov DWORD PTR [esp+24], eax
	mov eax, 3168
	mov DWORD PTR [esp+28], eax
	mov eax, 3168
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 881
	mov DWORD PTR [esp+4], eax
	mov eax, 48
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 840
	mov DWORD PTR [esp+20], eax
	mov eax, 3168
	mov DWORD PTR [esp+24], eax
	mov eax, 3168
	mov DWORD PTR [esp+28], eax
	mov eax, 3168
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 881
	mov DWORD PTR [esp+4], eax
	mov eax, 48
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 840
	mov DWORD PTR [esp+20], eax
	mov eax, 3168
	mov DWORD PTR [esp+24], eax
	mov eax, 3168
	mov DWORD PTR [esp+28], eax
	mov eax, 3168
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 881
	mov DWORD PTR [esp+4], eax
	mov eax, 48
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 840
	mov DWORD PTR [esp+20], eax
	mov eax, 3168
	mov DWORD PTR [esp+24], eax
	mov eax, 3168
	mov DWORD PTR [esp+28], eax
	mov eax, 3168
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 881
	mov DWORD PTR [esp+4], eax
	mov eax, 48
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 840
	mov DWORD PTR [esp+20], eax
	mov eax, 3168
	mov DWORD PTR [esp+24], eax
	mov eax, 3168
	mov DWORD PTR [esp+28], eax
	mov eax, 3168
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, 0
	mov ebp, edi
213:
	mov eax, DWORD PTR [ebp+3944]
	mov edx, DWORD PTR [ebp+3944]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+5496], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 213b
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 881
	mov DWORD PTR [esp+4], eax
	mov eax, 48
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 840
	mov DWORD PTR [esp+20], eax
	mov eax, 3944
	mov DWORD PTR [esp+24], eax
	mov eax, 3944
	mov DWORD PTR [esp+28], eax
	mov eax, 3168
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 881
	mov DWORD PTR [esp+4], eax
	mov eax, 48
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 840
	mov DWORD PTR [esp+20], eax
	mov eax, 5496
	mov DWORD PTR [esp+24], eax
	mov eax, 5496
	mov DWORD PTR [esp+28], eax
	mov eax, 3168
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 0
	mov ebp, edi
214:
	mov DWORD PTR [ebp+4720], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 214b
	mov eax, 1
	mov DWORD PTR [edi+4720], eax
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 881
	mov DWORD PTR [esp+4], eax
	mov eax, 48
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 840
	mov DWORD PTR [esp+20], eax
	mov eax, 4720
	mov DWORD PTR [esp+24], eax
	mov eax, 3168
	mov DWORD PTR [esp+28], eax
	mov eax, 4720
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, 0
	mov ebp, edi
215:
	mov eax, DWORD PTR [ebp+4720]
	mov edx, DWORD PTR [ebp+4720]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+2392], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 215b
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 881
	mov DWORD PTR [esp+4], eax
	mov eax, 48
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 840
	mov DWORD PTR [esp+20], eax
	mov eax, 3168
	mov DWORD PTR [esp+24], eax
	mov eax, 3944
	mov DWORD PTR [esp+28], eax
	mov eax, 5496
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, 0
	mov ebp, edi
216:
	mov eax, DWORD PTR [ebp+3168]
	mov edx, DWORD PTR [ebp+3168]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+2776], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 216b
	mov ecx, 0
	mov ebp, edi
217:
	mov eax, DWORD PTR [ebp+5496]
	mov edx, DWORD PTR [ebp+5496]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+3168], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 217b
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 881
	mov DWORD PTR [esp+4], eax
	mov eax, 48
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 840
	mov DWORD PTR [esp+20], eax
	mov eax, 5496
	mov DWORD PTR [esp+24], eax
	mov eax, 3168
	mov DWORD PTR [esp+28], eax
	mov eax, 3944
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, 0
	mov ebp, edi
218:
	mov eax, DWORD PTR [ebp+5496]
	mov edx, DWORD PTR [ebp+5496]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+3168], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 218b
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 881
	mov DWORD PTR [esp+4], eax
	mov eax, 48
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 840
	mov DWORD PTR [esp+20], eax
	mov eax, 5496
	mov DWORD PTR [esp+24], eax
	mov eax, 5496
	mov DWORD PTR [esp+28], eax
	mov eax, 3944
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, 0
	mov ebp, edi
219:
	mov eax, DWORD PTR [ebp+5496]
	mov edx, DWORD PTR [ebp+5496]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+2776], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 219b
	mov esi, 128
220:
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 881
	mov DWORD PTR [esp+4], eax
	mov eax, 48
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 840
	mov DWORD PTR [esp+20], eax
	mov eax, 4720
	mov DWORD PTR [esp+24], eax
	mov eax, 4720
	mov DWORD PTR [esp+28], eax
	mov eax, 4720
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 881
	mov DWORD PTR [esp+4], eax
	mov eax, 48
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 840
	mov DWORD PTR [esp+20], eax
	mov eax, 4720
	mov DWORD PTR [esp+24], eax
	mov eax, 4720
	mov DWORD PTR [esp+28], eax
	mov eax, 4720
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, DWORD PTR [edi+6300]
	shr eax, 30
	mov DWORD PTR [edi+4], eax
	mov ecx, 0
	mov ebp, edi
221:
	mov eax, DWORD PTR [ebp+2392]
	mov edx, DWORD PTR [ebp+2392]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+5496], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 221b
	mov eax, DWORD PTR [edi+4]
	xor eax, 1
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, edi
222:
	mov eax, DWORD PTR [ebp+5496]
	mov edx, DWORD PTR [ebp+3944]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+5496], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 222b
	mov eax, DWORD PTR [edi+4]
	xor eax, 2
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, edi
223:
	mov eax, DWORD PTR [ebp+5496]
	mov edx, DWORD PTR [ebp+3168]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+5496], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 223b
	mov eax, DWORD PTR [edi+4]
	xor eax, 3
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, edi
224:
	mov eax, DWORD PTR [ebp+5496]
	mov edx, DWORD PTR [ebp+2776]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+5496], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 224b
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 881
	mov DWORD PTR [esp+4], eax
	mov eax, 48
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 840
	mov DWORD PTR [esp+20], eax
	mov eax, 4720
	mov DWORD PTR [esp+24], eax
	mov eax, 4720
	mov DWORD PTR [esp+28], eax
	mov eax, 5496
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, 0
	mov ebp, edi
225:
	mov eax, DWORD PTR [ebp+6272]
	mov ebx, eax
	shr ebx, 31
	add eax, eax
	add eax, ecx
	mov DWORD PTR [ebp+6272], eax
	mov ecx, ebx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 225b
	mov ecx, 0
	mov ebp, edi
226:
	mov eax, DWORD PTR [ebp+6272]
	mov ebx, eax
	shr ebx, 31
	add eax, eax
	add eax, ecx
	mov DWORD PTR [ebp+6272], eax
	mov ecx, ebx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 226b
	sub esi, 1
	cmp esi, 0
	jne 220b
	mov eax, 0
	mov ebp, edi
227:
	mov DWORD PTR [ebp+5496], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 227b
	mov eax, 1
	mov DWORD PTR [edi+5496], eax
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 881
	mov DWORD PTR [esp+4], eax
	mov eax, 48
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 840
	mov DWORD PTR [esp+20], eax
	mov eax, 4720
	mov DWORD PTR [esp+24], eax
	mov eax, 4720
	mov DWORD PTR [esp+28], eax
	mov eax, 5496
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ebx, DWORD PTR [edi+8]
	mov esi, DWORD PTR [edi+12]
	mov ebp, DWORD PTR [edi+16]
	mov edi, DWORD PTR [edi+20]
	ret
	.p2align 6
