// The functions of `src/internal/vg_mldsa_power2round.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_power2round:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+24]
	mov ebp, DWORD PTR [esp+28]
	mov ecx, 256
20:
	mov eax, DWORD PTR [esi]
	add eax, 4095
	mov edx, eax
	shr edx, 13
	mov DWORD PTR [edi], edx
	and eax, 8191
	sub eax, 4095
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [ebp], eax
	add esi, 4
	add edi, 4
	add ebp, 4
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
