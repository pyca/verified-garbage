// The functions of `src/internal/vg_blake2b_update_scratch.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_update_scratch:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+528], eax
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+532], ecx
	or ecx, eax
	je 20f
	sub eax, 1
	and eax, 127
	add eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	test edi, edi
	je 22f
	test eax, eax
	je 24f
	mov ecx, 128
	sub ecx, eax
	cmp edi, ecx
	jb 26f
	jmp 27f
26:
	mov ecx, edi
27:
	sub edi, ecx
	mov edx, ebx
	add edx, eax
	mov eax, DWORD PTR [ebp+528]
	add eax, ecx
	mov DWORD PTR [ebp+528], eax
	mov eax, DWORD PTR [ebp+532]
	adc eax, 0
	mov DWORD PTR [ebp+532], eax
	test ecx, ecx
	je 28f
210:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edx+64], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 210b
	jmp 29f
28:
29:
	test edi, edi
	je 211f
	mov DWORD PTR [ebp+536], esi
	mov DWORD PTR [ebp+540], edi
	mov esi, ebx
	add esi, 64
	mov edi, 1
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	mov eax, 0
	push ebp
	push eax
	push edx
	push ecx
	push edi
	push esi
	push ebx
	call {vg_blake2b_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [ebp+536]
	mov edi, DWORD PTR [ebp+540]
	jmp 212f
211:
212:
	jmp 25f
24:
25:
	test edi, edi
	je 213f
	mov eax, edi
	sub eax, 1
	mov ecx, eax
	and ecx, 127
	sub eax, ecx
	je 215f
	mov DWORD PTR [ebp+540], edi
	mov DWORD PTR [ebp+544], eax
	mov edi, eax
	shr edi, 7
	mov ecx, DWORD PTR [ebp+528]
	add ecx, 128
	mov edx, DWORD PTR [ebp+532]
	adc edx, 0
	mov eax, 0
	push ebp
	push eax
	push edx
	push ecx
	push edi
	push esi
	push ebx
	call {vg_blake2b_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+544]
	add esi, eax
	mov edi, DWORD PTR [ebp+540]
	sub edi, eax
	jmp 216f
215:
216:
	mov ecx, edi
	mov edx, ebx
217:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edx+64], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 217b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov eax, ebp
	mov ebx, DWORD PTR [eax+512]
	mov esi, DWORD PTR [eax+516]
	mov edi, DWORD PTR [eax+520]
	mov ebp, DWORD PTR [eax+524]
	ret
	.p2align 6
