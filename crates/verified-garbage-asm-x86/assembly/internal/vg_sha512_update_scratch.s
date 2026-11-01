// The functions of `src/internal/vg_sha512_update_scratch.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_update_scratch:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+224], ebx
	mov DWORD PTR [eax+228], esi
	mov DWORD PTR [eax+232], edi
	mov DWORD PTR [eax+236], ebp
	mov ebx, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+16]
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+8]
	and edi, 127
20:
	test edi, edi
	je 21f
	mov eax, 128
	sub eax, edi
	cmp esi, eax
	jb 23f
	jmp 24f
23:
	mov eax, esi
24:
	sub esi, eax
	add edi, ebx
	test eax, eax
	je 25f
27:
	movzx ecx, BYTE PTR [ebp]
	mov BYTE PTR [edi+64], cl
	add ebp, 1
	add edi, 1
	sub eax, 1
	jne 27b
	jmp 26f
25:
26:
	sub edi, ebx
	mov ecx, 0
	cmp edi, 128
	je 28f
	jmp 29f
28:
	mov eax, ebx
	add eax, 64
	mov edi, 0
	mov ecx, 1
29:
	jmp 22f
21:
	cmp esi, 128
	jae 210f
	mov eax, 128
	sub eax, edi
	cmp esi, eax
	jb 212f
	jmp 213f
212:
	mov eax, esi
213:
	sub esi, eax
	add edi, ebx
	test eax, eax
	je 214f
216:
	movzx ecx, BYTE PTR [ebp]
	mov BYTE PTR [edi+64], cl
	add ebp, 1
	add edi, 1
	sub eax, 1
	jne 216b
	jmp 215f
214:
215:
	sub edi, ebx
	mov ecx, 0
	cmp edi, 128
	je 217f
	jmp 218f
217:
	mov eax, ebx
	add eax, 64
	mov edi, 0
	mov ecx, 1
218:
	jmp 211f
210:
	mov eax, ebp
	mov ecx, esi
	and ecx, 127
	mov edx, esi
	sub edx, ecx
	add ebp, edx
	mov esi, ecx
	mov ecx, edx
	shr ecx, 7
211:
22:
	test ecx, ecx
	jne 219f
	jmp 220f
219:
	mov edx, DWORD PTR [esp+24]
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 1
	test ecx, ecx
220:
	jne 20b
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+224]
	mov esi, DWORD PTR [eax+228]
	mov edi, DWORD PTR [eax+232]
	mov ebp, DWORD PTR [eax+236]
	ret
	.p2align 6
