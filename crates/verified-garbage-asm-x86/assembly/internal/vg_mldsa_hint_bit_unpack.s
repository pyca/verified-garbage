// The functions of `src/internal/vg_mldsa_hint_bit_unpack.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_hint_bit_unpack:
	push ebx
	push esi
	push edi
	push ebp
	mov ecx, DWORD PTR [esp+32]
	mov edx, DWORD PTR [esp+36]
	mov eax, 0
20:
	mov DWORD PTR [ecx], eax
	add ecx, 4
	sub edx, 1
	jne 20b
	mov ecx, DWORD PTR [esp+32]
	mov edi, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
	sub edx, DWORD PTR [esp+28]
	mov esi, edi
	add esi, DWORD PTR [esp+28]
	mov DWORD PTR [esp+24], edx
	mov DWORD PTR [esp+36], esi
	mov esi, 1
21:
	mov edx, DWORD PTR [esp+36]
	movzx ebx, BYTE PTR [edx]
	cmp ebx, eax
	jb 22f
	mov edx, DWORD PTR [esp+28]
	cmp edx, ebx
	jb 24f
	cmp eax, ebx
	jb 26f
	jmp 27f
26:
	mov edx, edi
	add edx, eax
	movzx ebp, BYTE PTR [edx]
	add ebp, ebp
	add ebp, ebp
	add ebp, ecx
	mov DWORD PTR [ebp], esi
	add eax, 1
	cmp eax, ebx
	jb 28f
	jmp 29f
28:
210:
	mov edx, edi
	add edx, eax
	movzx ebp, BYTE PTR [edx]
	sub edx, 1
	movzx edx, BYTE PTR [edx]
	cmp edx, ebp
	jb 211f
	mov eax, 256
	jmp 212f
211:
	add ebp, ebp
	add ebp, ebp
	add ebp, ecx
	mov DWORD PTR [ebp], esi
	add eax, 1
212:
	cmp eax, ebx
	jb 210b
29:
27:
	jmp 25f
24:
	mov eax, 256
25:
	jmp 23f
22:
	mov eax, 256
23:
	mov edx, DWORD PTR [esp+36]
	add edx, 1
	mov DWORD PTR [esp+36], edx
	add ecx, 1024
	mov edx, DWORD PTR [esp+24]
	sub edx, 1
	mov DWORD PTR [esp+24], edx
	jne 21b
	cmp eax, DWORD PTR [esp+28]
	jb 213f
	jmp 214f
213:
215:
	mov edx, edi
	add edx, eax
	movzx edx, BYTE PTR [edx]
	cmp edx, 0
	jne 216f
	add eax, 1
	jmp 217f
216:
	mov eax, 256
217:
	cmp eax, DWORD PTR [esp+28]
	jb 215b
214:
	mov edx, DWORD PTR [esp+28]
	cmp edx, eax
	mov eax, 1
	sbb eax, 0
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
