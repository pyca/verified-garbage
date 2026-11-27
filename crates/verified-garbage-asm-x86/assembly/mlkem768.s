// The functions of `src/mlkem768.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_check_ek:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+20]
	mov ecx, 384
	mov ebx, -1
20:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [esi+1]
	mov ebp, edx
	and edx, 15
	ror edx, 24
	add eax, edx
	shr ebp, 4
	movzx edx, BYTE PTR [esi+2]
	ror edx, 28
	add ebp, edx
	sub eax, 3329
	sbb eax, eax
	and ebx, eax
	sub ebp, 3329
	sbb ebp, ebp
	and ebx, ebp
	add esi, 3
	sub ecx, 1
	jne 20b
	mov eax, ebx
	and eax, 1
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pxor xmm0, xmm0
	lea esp, [esp-16]
	movdqu XMMWORD PTR [esp], xmm0
	lea esp, [esp+16]
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_mlkem768_keygen:
	lea esp, [esp-28]
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+12], eax
	call {vg_mlkem768_keygen_body}
	mov DWORD PTR [esp+16], eax
	mov DWORD PTR [esp+20], edx
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp], eax
	mov eax, 32768
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize_core}
	mov eax, DWORD PTR [esp+16]
	mov edx, DWORD PTR [esp+20]
	lea esp, [esp+28]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-120]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	lea esp, [esp+120]
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_mlkem768_encaps:
	lea esp, [esp-28]
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp+16], eax
	call {vg_mlkem768_encaps_body}
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+24], edx
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp], eax
	mov eax, 32768
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize_core}
	mov eax, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
	lea esp, [esp+28]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-120]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	lea esp, [esp+120]
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_mlkem768_encaps_h:
	lea esp, [esp-44]
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+20], eax
	call {vg_mlkem768_encaps_h_body}
	mov DWORD PTR [esp+24], eax
	mov DWORD PTR [esp+28], edx
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp], eax
	mov eax, 32768
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize_core}
	mov eax, DWORD PTR [esp+24]
	mov edx, DWORD PTR [esp+28]
	lea esp, [esp+44]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-136]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	movdqu XMMWORD PTR [esp+112], xmm0
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	lea esp, [esp+136]
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_mlkem768_decaps:
	lea esp, [esp-28]
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+12], eax
	call {vg_mlkem768_decaps_body}
	mov DWORD PTR [esp+16], eax
	mov DWORD PTR [esp+20], edx
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp], eax
	mov eax, 32768
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize_core}
	mov eax, DWORD PTR [esp+16]
	mov edx, DWORD PTR [esp+20]
	lea esp, [esp+28]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-120]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	lea esp, [esp+120]
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6
