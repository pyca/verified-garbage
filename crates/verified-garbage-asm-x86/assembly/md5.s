// The functions of `src/md5.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_init:
	mov eax, DWORD PTR [esp+4]
	mov ecx, 1732584193
	mov DWORD PTR [eax], ecx
	mov ecx, -271733879
	mov DWORD PTR [eax+4], ecx
	mov ecx, -1732584194
	mov DWORD PTR [eax+8], ecx
	mov ecx, 271733878
	mov DWORD PTR [eax+12], ecx
	ret
	.p2align 6

vg_md5_update:
	lea esp, [esp-140]
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+152]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+156]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+160]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+64], ebx
	mov DWORD PTR [eax+68], esi
	mov DWORD PTR [eax+72], edi
	mov DWORD PTR [eax+76], ebp
	mov ebx, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+16]
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+8]
	and edi, 63
20:
	test edi, edi
	je 21f
	mov eax, 64
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
	mov BYTE PTR [edi+16], cl
	add ebp, 1
	add edi, 1
	sub eax, 1
	jne 27b
	jmp 26f
25:
26:
	sub edi, ebx
	mov ecx, 0
	cmp edi, 64
	je 28f
	jmp 29f
28:
	mov eax, ebx
	add eax, 16
	mov edi, 0
	mov ecx, 1
29:
	jmp 22f
21:
	cmp esi, 64
	jae 210f
	mov eax, 64
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
	mov BYTE PTR [edi+16], cl
	add ebp, 1
	add edi, 1
	sub eax, 1
	jne 216b
	jmp 215f
214:
215:
	sub edi, ebx
	mov ecx, 0
	cmp edi, 64
	je 217f
	jmp 218f
217:
	mov eax, ebx
	add eax, 16
	mov edi, 0
	mov ecx, 1
218:
	jmp 211f
210:
	mov eax, ebp
	mov ecx, esi
	and ecx, 63
	mov edx, esi
	sub edx, ecx
	add ebp, edx
	mov esi, ecx
	mov ecx, edx
	shr ecx, 6
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
	call {vg_md5_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 1
	test ecx, ecx
220:
	jne 20b
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+64]
	mov esi, DWORD PTR [eax+68]
	mov edi, DWORD PTR [eax+72]
	mov ebp, DWORD PTR [eax+76]
	lea esp, [esp+140]
	ret
	.p2align 6

vg_md5_finalize:
	lea esp, [esp-136]
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+152]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+64], ebx
	mov DWORD PTR [eax+68], esi
	mov DWORD PTR [eax+72], edi
	mov DWORD PTR [eax+76], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+80], ecx
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+84], ecx
	mov ecx, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+88], ecx
	mov edi, DWORD PTR [esp+8]
	and edi, 63
	mov edx, ebx
	add edx, edi
	mov ecx, 128
	mov BYTE PTR [edx+16], cl
	add edi, 1
	mov esi, 0
	cmp edi, 57
	jae 20f
	jmp 21f
20:
	mov esi, 1
21:
22:
	mov eax, 64
	test esi, esi
	je 23f
	jmp 24f
23:
	mov eax, 56
24:
	mov ecx, 0
	sub eax, edi
	je 25f
27:
	mov edx, ebx
	add edx, edi
	mov BYTE PTR [edx+16], cl
	add edi, 1
	sub eax, 1
	jne 27b
	jmp 26f
25:
26:
	test esi, esi
	je 28f
	jmp 29f
28:
	mov eax, DWORD PTR [ebp+80]
	mov ecx, DWORD PTR [ebp+84]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebx+72], eax
	mov DWORD PTR [ebx+76], ecx
29:
	mov eax, ebx
	add eax, 16
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_md5_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, 0
	sub esi, 1
	je 22b
	mov eax, DWORD PTR [ebp+88]
	mov ecx, DWORD PTR [ebx]
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	mov DWORD PTR [eax+12], ecx
	mov ebx, DWORD PTR [ebp+64]
	mov esi, DWORD PTR [ebp+68]
	mov edi, DWORD PTR [ebp+72]
	mov ebp, DWORD PTR [ebp+76]
	lea esp, [esp+136]
	ret
	.p2align 6
