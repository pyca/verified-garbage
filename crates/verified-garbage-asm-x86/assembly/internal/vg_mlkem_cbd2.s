// The functions of `src/internal/vg_mlkem_cbd2.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_cbd2:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+24]
	mov ecx, 128
20:
	movzx ebx, BYTE PTR [esi]
	mov eax, ebx
	mov edx, eax
	shr edx, 1
	and eax, 5
	and edx, 5
	add eax, edx
	mov edx, eax
	shr edx, 2
	and eax, 3
	add eax, 3329
	sub eax, edx
	sub eax, 3329
	sbb edx, edx
	and edx, 3329
	add eax, edx
	mov DWORD PTR [edi], eax
	mov eax, ebx
	shr eax, 4
	mov edx, eax
	shr edx, 1
	and eax, 5
	and edx, 5
	add eax, edx
	mov edx, eax
	shr edx, 2
	and eax, 3
	add eax, 3329
	sub eax, edx
	sub eax, 3329
	sbb edx, edx
	and edx, 3329
	add eax, edx
	mov DWORD PTR [edi+4], eax
	add esi, 1
	add edi, 8
	sub ecx, 1
	jne 20b
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
