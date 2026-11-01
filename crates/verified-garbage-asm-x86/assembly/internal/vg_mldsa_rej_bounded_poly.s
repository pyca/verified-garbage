// The functions of `src/internal/vg_mldsa_rej_bounded_poly.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_rej_bounded_poly:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+32]
	mov ebx, esi
	add ebx, 0
	mov eax, 0
	mov ecx, 50
20:
	mov DWORD PTR [ebx], eax
	add ebx, 4
	sub ecx, 1
	jne 20b
	mov eax, esi
	mov ecx, 136
	mov edx, 0
	mov ebx, DWORD PTR [esp+20]
	mov ebp, 66
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	mov ecx, 136
	mov edx, 66
	mov ebx, 31
	mov edi, esi
	add edi, 200
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_pad_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 840
	mov ebp, 544
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_squeeze_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+24]
	cmp eax, 2
	je 21f
	add esi, 840
	mov ecx, 0
	mov ebp, 544
23:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	and edx, 15
	cmp ecx, 256
	jb 24f
	jmp 25f
24:
	cmp edx, 9
	jb 26f
	jmp 27f
26:
	mov ebx, 4
	sub ebx, edx
	sbb edx, edx
	and edx, 8380417
	add ebx, edx
	mov DWORD PTR [edi], ebx
	add edi, 4
	add ecx, 1
27:
	shr eax, 4
	mov edx, eax
	cmp ecx, 256
	jb 28f
	jmp 29f
28:
	cmp edx, 9
	jb 210f
	jmp 211f
210:
	mov ebx, 4
	sub ebx, edx
	sbb edx, edx
	and edx, 8380417
	add ebx, edx
	mov DWORD PTR [edi], ebx
	add edi, 4
	add ecx, 1
211:
29:
25:
	add esi, 1
	sub ebp, 1
	jne 23b
	jmp 22f
21:
	add esi, 840
	mov ecx, 0
	mov ebp, 544
212:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	and edx, 15
	cmp ecx, 256
	jb 213f
	jmp 214f
213:
	cmp edx, 15
	jb 215f
	jmp 216f
215:
	sub edx, 10
	sbb ebx, ebx
	and ebx, 10
	add edx, ebx
	sub edx, 5
	sbb ebx, ebx
	and ebx, 5
	add edx, ebx
	mov ebx, 2
	sub ebx, edx
	sbb edx, edx
	and edx, 8380417
	add ebx, edx
	mov DWORD PTR [edi], ebx
	add edi, 4
	add ecx, 1
216:
	shr eax, 4
	mov edx, eax
	cmp ecx, 256
	jb 217f
	jmp 218f
217:
	cmp edx, 15
	jb 219f
	jmp 220f
219:
	sub edx, 10
	sbb ebx, ebx
	and ebx, 10
	add edx, ebx
	sub edx, 5
	sbb ebx, ebx
	and ebx, 5
	add edx, ebx
	mov ebx, 2
	sub ebx, edx
	sbb edx, edx
	and edx, 8380417
	add ebx, edx
	mov DWORD PTR [edi], ebx
	add edi, 4
	add ecx, 1
220:
218:
214:
	add esi, 1
	sub ebp, 1
	jne 212b
22:
	mov eax, ecx
	shr eax, 8
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
