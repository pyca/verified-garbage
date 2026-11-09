// The functions of `src/internal/vg_rsa_private_checked.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_private_checked:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-3328]
	mov eax, esp
	add eax, 128
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+3352]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+3356]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+3360]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+3372]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+3376]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+3380]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+3384]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+3388]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+3392]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+3396]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+3400]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+3404]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+3408]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+3412]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+3416]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+3420]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+3424]
	mov DWORD PTR [esp+68], eax
	call {vg_rsa_private_crt}
	mov DWORD PTR [esp+80], eax
	mov eax, esp
	add eax, 1152
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+3360]
	add eax, 7
	shr eax, 3
	add eax, eax
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+3356]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+3360]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+3420]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+3424]
	mov DWORD PTR [esp+20], eax
	call {vg_rsa_public_precompute}
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+3348]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+3352]
	mov DWORD PTR [esp+4], eax
	mov eax, esp
	add eax, 1152
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+3360]
	add eax, 7
	shr eax, 3
	add eax, eax
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+3364]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+3368]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 128
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+3376]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+3420]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+3424]
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	and eax, DWORD PTR [esp+80]
	and eax, DWORD PTR [esp+84]
	and eax, 1
	mov ebx, eax
	mov esi, DWORD PTR [esp+3348]
	mov edi, DWORD PTR [esp+3372]
	mov ecx, DWORD PTR [esp+3360]
	mov ebp, 0
20:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 20b
	mov eax, 0
	sub eax, ebp
	or eax, ebp
	shr eax, 31
	xor eax, 1
	mov edx, ebx
	and edx, eax
	mov ebp, 0
	sub ebp, edx
	mov edx, ebp
	mov ebp, 0
	sub ebp, ebx
	mov ebx, 2
	sub ebx, eax
	and ebx, ebp
	mov edi, DWORD PTR [esp+3348]
	mov esi, esp
	add esi, 128
	mov ecx, DWORD PTR [esp+3360]
21:
	movzx eax, BYTE PTR [esi]
	and eax, edx
	mov BYTE PTR [edi], al
	mov eax, 0
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 21b
	mov eax, ebx
	lea esp, [esp+3328]
	mov edi, DWORD PTR [esp]
	mov ebp, DWORD PTR [esp+8]
	mov esi, DWORD PTR [esp+4]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
