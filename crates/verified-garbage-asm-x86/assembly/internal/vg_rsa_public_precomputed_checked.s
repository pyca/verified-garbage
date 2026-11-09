// The functions of `src/internal/vg_rsa_public_precomputed_checked.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_public_precomputed_checked:
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], ebp
	mov DWORD PTR [eax+8], esi
	mov DWORD PTR [eax+12], edi
	mov edi, eax
	mov esi, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	mov ebx, 0
	mov edx, 0
20:
	movzx eax, BYTE PTR [esi]
	mov ebp, ebx
	shr ebp, 24
	ror edx, 24
	and edx, -256
	add edx, ebp
	ror ebx, 24
	and ebx, -256
	add ebx, eax
	mov ebp, edx
	shr ebp, 1
	cmp ebp, 0
	je 21f
	mov edx, 2
	jmp 22f
21:
22:
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 20b
	mov ebp, edx
	shr ebp, 1
	mov eax, ebx
	and eax, 1
	xor eax, 1
	or ebp, eax
	cmp ebp, 0
	je 23f
	mov eax, 0
	jmp 24f
23:
	mov ebp, ebx
	xor ebp, 1
	or ebp, edx
	cmp ebp, 0
	je 25f
	mov eax, 1
	jmp 26f
25:
	mov eax, 0
26:
24:
	cmp eax, 0
	je 27f
	mov DWORD PTR [edi+128], ebx
	mov DWORD PTR [edi+132], edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov ebp, edi
	add ebp, 256
	mov esi, DWORD PTR [esp+12]
29:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 29b
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov ebp, edi
	add ebp, 256
	add ebp, ecx
	add ebp, ecx
	add ebp, ecx
	add ebp, ecx
	mov esi, DWORD PTR [esp+12]
	add esi, ecx
210:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 210b
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov ebp, edi
	add ebp, 256
	add ebp, ecx
	add ebp, ecx
	add ebp, ecx
	mov eax, 0
211:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 211b
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, edi
	add eax, 256
	add eax, ecx
	add eax, ecx
	add eax, ecx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov esi, edi
	add esi, 256
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebp, edi
	add ebp, 256
	mov ecx, 0
212:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 212b
	mov DWORD PTR [edi+148], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov esi, edi
	add esi, 256
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebp, edi
	add ebp, 256
	mov ecx, 0
213:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 213b
	mov edx, DWORD PTR [edi+148]
	and ecx, edx
	mov eax, DWORD PTR [edi+256]
	and eax, 1
	and ecx, eax
	cmp ecx, 0
	je 214f
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov ebp, edi
	add ebp, 256
	add ebp, ecx
	mov eax, 0
216:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 216b
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov ebx, edi
	add ebx, 256
	add ebx, ecx
	mov esi, DWORD PTR [esp+28]
	mov ecx, DWORD PTR [esp+32]
	add esi, ecx
	sub esi, 1
217:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 217b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov esi, edi
	add esi, 256
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebp, edi
	add ebp, 256
	mov ecx, 0
218:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 218b
	mov DWORD PTR [edi+144], ecx
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
	mov DWORD PTR [edi+152], eax
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	mov eax, 256
	mov DWORD PTR [esp+12], eax
	mov eax, 152
	mov DWORD PTR [esp+16], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 256
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 256
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, DWORD PTR [edi+128]
	and ecx, 1
	cmp ecx, 0
	je 219f
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov esi, edi
	add esi, 256
	add esi, ecx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov ebp, edi
	add ebp, 256
	add ebp, ecx
	add ebp, ecx
221:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 221b
	mov eax, DWORD PTR [edi+128]
	sub eax, 1
	mov DWORD PTR [edi+128], eax
	jmp 220f
219:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	mov eax, 256
	mov DWORD PTR [esp+12], eax
	mov eax, 152
	mov DWORD PTR [esp+16], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
220:
222:
	mov ecx, DWORD PTR [edi+128]
	and ecx, 1
	cmp ecx, 0
	je 223f
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	mov eax, 256
	mov DWORD PTR [esp+12], eax
	mov eax, 152
	mov DWORD PTR [esp+16], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 256
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	jmp 224f
223:
224:
	mov eax, DWORD PTR [edi+132]
	and eax, 1
	ror eax, 1
	mov edx, DWORD PTR [edi+128]
	shr edx, 1
	add edx, eax
	mov DWORD PTR [edi+128], edx
	mov eax, 0
	and eax, 1
	ror eax, 1
	mov edx, DWORD PTR [edi+132]
	shr edx, 1
	add edx, eax
	mov DWORD PTR [edi+132], edx
	mov eax, DWORD PTR [edi+128]
	or eax, DWORD PTR [edi+132]
	cmp eax, 0
	je 225f
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	mov eax, 256
	mov DWORD PTR [esp+12], eax
	mov eax, 152
	mov DWORD PTR [esp+16], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 256
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 256
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 256
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, DWORD PTR [edi+128]
	or eax, DWORD PTR [edi+132]
	cmp eax, 0
	jmp 226f
225:
226:
	jne 222b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	mov eax, 256
	mov DWORD PTR [esp+12], eax
	mov eax, 152
	mov DWORD PTR [esp+16], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebp, edi
	add ebp, 256
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [edi+144]
227:
	mov eax, DWORD PTR [ebp]
	and eax, ecx
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub edx, 4
	jne 227b
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov esi, edi
	add esi, 256
	add esi, edx
	add esi, edx
	add esi, ecx
	sub esi, 1
228:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 228b
	mov eax, DWORD PTR [edi+144]
	and eax, 1
	jmp 215f
214:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov eax, 0
229:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 229b
215:
	jmp 28f
27:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov eax, 0
230:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 230b
28:
	mov ebx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi+4]
	mov esi, DWORD PTR [edi+8]
	mov edi, DWORD PTR [edi+12]
	ret
	.p2align 6
