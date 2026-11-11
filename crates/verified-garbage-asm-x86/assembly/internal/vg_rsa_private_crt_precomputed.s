// The functions of `src/internal/vg_rsa_private_crt_precomputed.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_private_crt_precomputed:
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [eax+32], ebx
	mov DWORD PTR [eax+36], ebp
	mov DWORD PTR [eax+40], esi
	mov DWORD PTR [eax+44], edi
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	movzx eax, BYTE PTR [esi]
	mov ebx, esi
	add ebx, ecx
	sub ebx, 1
	movzx edx, BYTE PTR [ebx]
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov ebp, ecx
	sub ebp, 64
	ror ebp, 24
	add ebp, eax
	sub ebp, 128
	shr ebp, 31
	and edx, 1
	xor edx, 1
	or ebx, edx
	or ebx, ebp
	cmp ebx, 0
	je 20f
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov eax, 0
22:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 22b
	jmp 21f
20:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
23:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 23b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	add esi, ecx
	sub esi, 1
24:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 24b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
25:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 25b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	add esi, ecx
	sub esi, 1
26:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 26b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
27:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 27b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+28]
	mov ecx, DWORD PTR [esp+32]
	add esi, ecx
	sub esi, 1
28:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 28b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
29:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 29b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+36]
	mov ecx, DWORD PTR [esp+40]
	add esi, ecx
	sub esi, 1
210:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 210b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
211:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 211b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+44]
	mov ecx, DWORD PTR [esp+48]
	add esi, ecx
	sub esi, 1
212:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 212b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
213:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 213b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+52]
	mov ecx, DWORD PTR [esp+56]
	add esi, ecx
	sub esi, 1
214:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 214b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
215:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 215b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+60]
	mov ecx, DWORD PTR [esp+64]
	add esi, ecx
	sub esi, 1
216:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 216b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
217:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 217b
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
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
	mov eax, DWORD PTR [edi+8]
	and eax, ecx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [edi+20], eax
	mov eax, 2
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+16]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 1
	cmp eax, edx
	jb 219f
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
221:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 221b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
222:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 222b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
223:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 223b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
224:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 224b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
225:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 225b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 3
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
226:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 226b
	mov edx, DWORD PTR [edi+3336]
	and edx, 1
	mov eax, 0
	sub eax, edx
	and ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
227:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 227b
	mov edi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [edi+3336]
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
228:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 228b
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	mov eax, ecx
	sub eax, 2
	sbb eax, eax
	and eax, 1
	add ecx, eax
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov esi, DWORD PTR [esp+76]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, eax
	add ebp, eax
	add ebp, eax
	add ebp, eax
229:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 229b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	mov eax, edx
	sub eax, 2
	sbb eax, eax
	and eax, 1
	add edx, eax
	add edx, edx
	add edx, edx
	add edx, edx
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	sub esi, edx
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	je 230f
232:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
233:
	cmp edx, 32
	jae 234f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
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
235:
	cmp edx, 0
	jne 233b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
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
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
239:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 239b
	and edi, 15
	jne 240f
	jmp 241f
240:
242:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 242b
241:
	mov edi, DWORD PTR [esp+68]
	sub esi, 1
	jne 232b
	jmp 231f
230:
231:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
243:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 243b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
244:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 244b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
245:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 245b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add esi, edx
246:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ebx, esi
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
247:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 247b
	mov edi, DWORD PTR [esp+68]
	mov esi, ebx
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp esi, edx
	jne 246b
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
248:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
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
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	sub eax, 4
	mov eax, DWORD PTR [eax]
	shr eax, 28
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
249:
	mov eax, DWORD PTR [ebp]
	mov ebx, eax
	shr ebx, 28
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, ecx
	mov DWORD PTR [ebp], eax
	mov ecx, ebx
	add ebp, 4
	sub edx, 4
	jne 249b
	mov eax, DWORD PTR [edi+4]
	add eax, 16
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
250:
	mov eax, DWORD PTR [edi+4]
	xor eax, 16
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+4]
	sub eax, 1
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
251:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 251b
	and edi, 15
	jne 252f
	jmp 253f
252:
254:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 254b
253:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp ebp, edx
	jne 250b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	jne 248b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
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
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
255:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 255b
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
256:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 256b
	mov edi, DWORD PTR [esp+68]
	jmp 220f
219:
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
257:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 257b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
258:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 258b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	shr ecx, 3
	add ecx, 1
	shr ecx, 1
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
259:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 259b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	shr ecx, 3
	add ecx, 1
	shr ecx, 1
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
260:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 260b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 3
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
261:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 261b
	mov edx, DWORD PTR [edi+3336]
	and edx, 1
	mov eax, 0
	sub eax, edx
	and ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
262:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 262b
	mov edi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [edi+3336]
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	shr ecx, 3
	add ecx, 1
	shr ecx, 1
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
263:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 263b
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	mov eax, ecx
	sub eax, 2
	sbb eax, eax
	and eax, 1
	add ecx, eax
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov esi, DWORD PTR [esp+76]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	shr eax, 3
	add eax, 1
	shr eax, 1
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, eax
	add ebp, eax
	add ebp, eax
	add ebp, eax
264:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 264b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	mov eax, edx
	sub eax, 2
	sbb eax, eax
	and eax, 1
	add edx, eax
	add edx, edx
	add edx, edx
	add edx, edx
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	shr esi, 3
	add esi, 1
	shr esi, 1
	add esi, esi
	add esi, esi
	add esi, esi
	sub esi, edx
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	je 265f
267:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
268:
	cmp edx, 32
	jae 269f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 270f
269:
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
270:
	cmp edx, 0
	jne 268b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
271:
	cmp edx, 32
	jae 272f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 273f
272:
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
273:
	cmp edx, 0
	jne 271b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
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
	mov edi, DWORD PTR [esp+68]
	sub esi, 1
	jne 267b
	jmp 266f
265:
266:
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
278:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 278b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
279:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 279b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
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
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
280:
	cmp edx, 32
	jae 281f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 282f
281:
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
282:
	cmp edx, 0
	jne 280b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
283:
	cmp edx, 32
	jae 284f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 285f
284:
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
285:
	cmp edx, 0
	jne 283b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
286:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 286b
	and edi, 15
	jne 287f
	jmp 288f
287:
289:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 289b
288:
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
290:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 290b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
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
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
292:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 292b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add esi, edx
293:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ebx, esi
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
294:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 294b
	mov edi, DWORD PTR [esp+68]
	mov esi, ebx
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	shr eax, 3
	add eax, 1
	shr eax, 1
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp esi, edx
	jne 293b
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	shr esi, 3
	add esi, 1
	shr esi, 1
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
295:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
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
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	sub eax, 4
	mov eax, DWORD PTR [eax]
	shr eax, 28
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
296:
	mov eax, DWORD PTR [ebp]
	mov ebx, eax
	shr ebx, 28
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, ecx
	mov DWORD PTR [ebp], eax
	mov ecx, ebx
	add ebp, 4
	sub edx, 4
	jne 296b
	mov eax, DWORD PTR [edi+4]
	add eax, 16
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
297:
	mov eax, DWORD PTR [edi+4]
	xor eax, 16
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+4]
	sub eax, 1
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
298:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 298b
	and edi, 15
	jne 299f
	jmp 2100f
299:
2101:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2101b
2100:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	shr eax, 3
	add eax, 1
	shr eax, 1
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp ebp, edx
	jne 297b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	jne 295b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
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
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2102:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2102b
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
2103:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2103b
	mov edi, DWORD PTR [esp+68]
220:
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
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
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2105:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2105b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2106:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2106b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2107:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2107b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2108:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2108b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2109:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2109b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
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
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
2111:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2111b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
2112:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2112b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+16]
	mov ecx, DWORD PTR [edi+20]
	mov DWORD PTR [edi+16], ecx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	sub eax, 1
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+16]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 1
	cmp eax, edx
	jb 2113f
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2115:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2115b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2116:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2116b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
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
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2118:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2118b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2119:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2119b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 3
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2120:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2120b
	mov edx, DWORD PTR [edi+3336]
	and edx, 1
	mov eax, 0
	sub eax, edx
	and ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2121:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2121b
	mov edi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [edi+3336]
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2122:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2122b
	mov ecx, DWORD PTR [esp+40]
	add ecx, 7
	shr ecx, 3
	mov eax, ecx
	sub eax, 2
	sbb eax, eax
	and eax, 1
	add ecx, eax
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov esi, DWORD PTR [esp+76]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	mov eax, edx
	sub eax, 2
	sbb eax, eax
	and eax, 1
	add edx, eax
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, eax
	add ebp, eax
	add ebp, eax
	add ebp, eax
2123:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 2123b
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	mov eax, edx
	sub eax, 2
	sbb eax, eax
	and eax, 1
	add edx, eax
	add edx, edx
	add edx, edx
	add edx, edx
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	sub esi, edx
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	je 2124f
2126:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2127:
	cmp edx, 32
	jae 2128f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2129f
2128:
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
2129:
	cmp edx, 0
	jne 2127b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2130:
	cmp edx, 32
	jae 2131f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2132f
2131:
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
2132:
	cmp edx, 0
	jne 2130b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
2133:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2133b
	and edi, 15
	jne 2134f
	jmp 2135f
2134:
2136:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2136b
2135:
	mov edi, DWORD PTR [esp+68]
	sub esi, 1
	jne 2126b
	jmp 2125f
2124:
2125:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2137:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2137b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2138:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2138b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2139:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2139b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add esi, edx
2140:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ebx, esi
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2141:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2141b
	mov edi, DWORD PTR [esp+68]
	mov esi, ebx
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp esi, edx
	jne 2140b
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2142:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
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
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	sub eax, 4
	mov eax, DWORD PTR [eax]
	shr eax, 28
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2143:
	mov eax, DWORD PTR [ebp]
	mov ebx, eax
	shr ebx, 28
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, ecx
	mov DWORD PTR [ebp], eax
	mov ecx, ebx
	add ebp, 4
	sub edx, 4
	jne 2143b
	mov eax, DWORD PTR [edi+4]
	add eax, 16
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
2144:
	mov eax, DWORD PTR [edi+4]
	xor eax, 16
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+4]
	sub eax, 1
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
2145:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2145b
	and edi, 15
	jne 2146f
	jmp 2147f
2146:
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
2147:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp ebp, edx
	jne 2144b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	jne 2142b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
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
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2149:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2149b
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2150:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2150b
	mov edi, DWORD PTR [esp+68]
	jmp 2114f
2113:
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
2151:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2151b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
2152:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2152b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	shr ecx, 3
	add ecx, 1
	shr ecx, 1
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2153:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2153b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	shr ecx, 3
	add ecx, 1
	shr ecx, 1
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2154:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2154b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 3
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2155:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2155b
	mov edx, DWORD PTR [edi+3336]
	and edx, 1
	mov eax, 0
	sub eax, edx
	and ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
2156:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2156b
	mov edi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [edi+3336]
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	shr ecx, 3
	add ecx, 1
	shr ecx, 1
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2157:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2157b
	mov ecx, DWORD PTR [esp+40]
	add ecx, 7
	shr ecx, 3
	mov eax, ecx
	sub eax, 2
	sbb eax, eax
	and eax, 1
	add ecx, eax
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov esi, DWORD PTR [esp+76]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	mov eax, edx
	sub eax, 2
	sbb eax, eax
	and eax, 1
	add edx, eax
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	shr eax, 3
	add eax, 1
	shr eax, 1
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, eax
	add ebp, eax
	add ebp, eax
	add ebp, eax
2158:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 2158b
	mov edx, DWORD PTR [esp+40]
	add edx, 7
	shr edx, 3
	mov eax, edx
	sub eax, 2
	sbb eax, eax
	and eax, 1
	add edx, eax
	add edx, edx
	add edx, edx
	add edx, edx
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	shr esi, 3
	add esi, 1
	shr esi, 1
	add esi, esi
	add esi, esi
	add esi, esi
	sub esi, edx
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	je 2159f
2161:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2162:
	cmp edx, 32
	jae 2163f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2164f
2163:
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
2164:
	cmp edx, 0
	jne 2162b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2165:
	cmp edx, 32
	jae 2166f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2167f
2166:
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
2167:
	cmp edx, 0
	jne 2165b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
2168:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2168b
	and edi, 15
	jne 2169f
	jmp 2170f
2169:
2171:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2171b
2170:
	mov edi, DWORD PTR [esp+68]
	sub esi, 1
	jne 2161b
	jmp 2160f
2159:
2160:
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
2172:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2172b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
2173:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2173b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
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
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2174:
	cmp edx, 32
	jae 2175f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2176f
2175:
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
2176:
	cmp edx, 0
	jne 2174b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2177:
	cmp edx, 32
	jae 2178f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2179f
2178:
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
2179:
	cmp edx, 0
	jne 2177b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
2180:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2180b
	and edi, 15
	jne 2181f
	jmp 2182f
2181:
2183:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2183b
2182:
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
2184:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2184b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
2185:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2185b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
2186:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2186b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add esi, edx
2187:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ebx, esi
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
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
	mov edi, DWORD PTR [esp+68]
	mov esi, ebx
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	shr eax, 3
	add eax, 1
	shr eax, 1
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp esi, edx
	jne 2187b
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	shr esi, 3
	add esi, 1
	shr esi, 1
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2189:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
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
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	sub eax, 4
	mov eax, DWORD PTR [eax]
	shr eax, 28
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2190:
	mov eax, DWORD PTR [ebp]
	mov ebx, eax
	shr ebx, 28
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, ecx
	mov DWORD PTR [ebp], eax
	mov ecx, ebx
	add ebp, 4
	sub edx, 4
	jne 2190b
	mov eax, DWORD PTR [edi+4]
	add eax, 16
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
2191:
	mov eax, DWORD PTR [edi+4]
	xor eax, 16
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+4]
	sub eax, 1
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
2192:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2192b
	and edi, 15
	jne 2193f
	jmp 2194f
2193:
2195:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2195b
2194:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	shr eax, 3
	add eax, 1
	shr eax, 1
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp ebp, edx
	jne 2191b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	jne 2189b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
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
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2196:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2196b
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
2197:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2197b
	mov edi, DWORD PTR [esp+68]
2114:
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2198:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2198b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2199:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2199b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2200:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2200b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2201:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2201b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2202:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2202b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2203:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2203b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
2204:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2204b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
2205:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2205b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
2206:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2206b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+16]
	mov ecx, DWORD PTR [edi+20]
	mov DWORD PTR [edi+16], ecx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	sub eax, 1
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+16]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 1
	cmp eax, edx
	jb 2207f
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2209:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2209b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2210:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2210b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2211:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2211b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 3
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2212:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2212b
	mov edx, DWORD PTR [edi+3336]
	and edx, 1
	mov eax, 0
	sub eax, edx
	and ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2213:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2213b
	mov edi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [edi+3336]
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2214:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2214b
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	mov eax, ecx
	sub eax, 2
	sbb eax, eax
	and eax, 1
	add ecx, eax
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov esi, DWORD PTR [esp+76]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, eax
	add ebp, eax
	add ebp, eax
	add ebp, eax
2215:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 2215b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	mov eax, edx
	sub eax, 2
	sbb eax, eax
	and eax, 1
	add edx, eax
	add edx, edx
	add edx, edx
	add edx, edx
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	sub esi, edx
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	je 2216f
2218:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2219:
	cmp edx, 32
	jae 2220f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2221f
2220:
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
2221:
	cmp edx, 0
	jne 2219b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2222:
	cmp edx, 32
	jae 2223f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2224f
2223:
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
2224:
	cmp edx, 0
	jne 2222b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
2225:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2225b
	and edi, 15
	jne 2226f
	jmp 2227f
2226:
2228:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2228b
2227:
	mov edi, DWORD PTR [esp+68]
	sub esi, 1
	jne 2218b
	jmp 2217f
2216:
2217:
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2229:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2229b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2230:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2230b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2231:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2231b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
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
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2232:
	cmp edx, 32
	jae 2233f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2234f
2233:
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
2234:
	cmp edx, 0
	jne 2232b
	mov edi, DWORD PTR [esp+68]
	mov DWORD PTR [edi+12], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2235:
	cmp edx, 32
	jae 2236f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2237f
2236:
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
2237:
	cmp edx, 0
	jne 2235b
	mov edi, DWORD PTR [esp+68]
	mov ecx, DWORD PTR [edi+12]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
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
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	jmp 2208f
2207:
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
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
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	shr ecx, 3
	add ecx, 1
	shr ecx, 1
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2240:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2240b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	shr ecx, 3
	add ecx, 1
	shr ecx, 1
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2241:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2241b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 3
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2242:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2242b
	mov edx, DWORD PTR [edi+3336]
	and edx, 1
	mov eax, 0
	sub eax, edx
	and ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
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
	mov edi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [edi+3336]
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	shr ecx, 3
	add ecx, 1
	shr ecx, 1
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2244:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2244b
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	mov eax, ecx
	sub eax, 2
	sbb eax, eax
	and eax, 1
	add ecx, eax
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov esi, DWORD PTR [esp+76]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	shr eax, 3
	add eax, 1
	shr eax, 1
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, eax
	add ebp, eax
	add ebp, eax
	add ebp, eax
2245:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 2245b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	mov eax, edx
	sub eax, 2
	sbb eax, eax
	and eax, 1
	add edx, eax
	add edx, edx
	add edx, edx
	add edx, edx
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	shr esi, 3
	add esi, 1
	shr esi, 1
	add esi, esi
	add esi, esi
	add esi, esi
	sub esi, edx
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	je 2246f
2248:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2249:
	cmp edx, 32
	jae 2250f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2251f
2250:
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
2251:
	cmp edx, 0
	jne 2249b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2252:
	cmp edx, 32
	jae 2253f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2254f
2253:
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
2254:
	cmp edx, 0
	jne 2252b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
2255:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2255b
	and edi, 15
	jne 2256f
	jmp 2257f
2256:
2258:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2258b
2257:
	mov edi, DWORD PTR [esp+68]
	sub esi, 1
	jne 2248b
	jmp 2247f
2246:
2247:
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
2259:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2259b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
2260:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2260b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
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
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2261:
	cmp edx, 32
	jae 2262f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2263f
2262:
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
2263:
	cmp edx, 0
	jne 2261b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2264:
	cmp edx, 32
	jae 2265f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2266f
2265:
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
2266:
	cmp edx, 0
	jne 2264b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
2267:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2267b
	and edi, 15
	jne 2268f
	jmp 2269f
2268:
2270:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2270b
2269:
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
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
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
2272:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2272b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
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
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2273:
	cmp edx, 32
	jae 2274f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2275f
2274:
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
2275:
	cmp edx, 0
	jne 2273b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2276:
	cmp edx, 32
	jae 2277f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2278f
2277:
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
2278:
	cmp edx, 0
	jne 2276b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
2279:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2279b
	and edi, 15
	jne 2280f
	jmp 2281f
2280:
2282:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2282b
2281:
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
2283:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2283b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2284:
	cmp edx, 32
	jae 2285f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2286f
2285:
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
2286:
	cmp edx, 0
	jne 2284b
	mov edi, DWORD PTR [esp+68]
	mov DWORD PTR [edi+12], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2287:
	cmp edx, 32
	jae 2288f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2289f
2288:
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
2289:
	cmp edx, 0
	jne 2287b
	mov edi, DWORD PTR [esp+68]
	mov ecx, DWORD PTR [edi+12]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
2290:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2290b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
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
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2291:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2291b
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	shr edx, 3
	add edx, 1
	shr edx, 1
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 3
	add edi, 1
	shr edi, 1
	add edi, edi
	add edi, edi
	add edi, edi
2292:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2292b
	mov edi, DWORD PTR [esp+68]
2208:
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ebx, edi
	add ebx, 2312
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2293:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2293b
	mov edi, DWORD PTR [esp+68]
	mov ebp, edi
	add ebp, 256
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2294:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2294b
	mov ebp, edi
	add ebp, 256
2295:
	mov eax, DWORD PTR [ebp+2056]
	mov DWORD PTR [edi+48], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ecx, edi
	add ecx, 3336
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	mov ebx, 0
2296:
	mov eax, DWORD PTR [edi+48]
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
	jne 2296b
	mov DWORD PTR [ebp], ebx
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	sub ebp, eax
	add ebp, 4
	add eax, edi
	add eax, 256
	cmp ebp, eax
	jne 2295b
	mov ebp, edi
	add ebp, 256
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2297:
	cmp edx, 32
	jae 2298f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2299f
2298:
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
2299:
	cmp edx, 0
	jne 2297b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, DWORD PTR [edi+8]
2300:
	mov eax, DWORD PTR [ebp]
	and eax, ecx
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub edx, 4
	jne 2300b
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
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
2301:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2301b
	mov eax, DWORD PTR [edi+8]
	and eax, 1
21:
	mov ebx, DWORD PTR [edi+32]
	mov ebp, DWORD PTR [edi+36]
	mov esi, DWORD PTR [edi+40]
	mov edi, DWORD PTR [edi+44]
	ret
	.p2align 6
