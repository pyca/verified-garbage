// The functions of `src/aes_ecb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ecb_encrypt_aesni:
	mov eax, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esp+12]
	mov ecx, edx
	sub ecx, eax
	shr ecx, 4
	add ecx, 5
	mov eax, DWORD PTR [esp+16]
	cmp ecx, eax
	mov ecx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	jae 20f
22:
	movdqu xmm0, XMMWORD PTR [edx]
	movdqu xmm1, XMMWORD PTR [edx+16]
	movdqu xmm2, XMMWORD PTR [edx+32]
	movdqu xmm3, XMMWORD PTR [edx+48]
	movdqu xmm4, XMMWORD PTR [edx+64]
	movdqu xmm5, XMMWORD PTR [edx+80]
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm0, xmm6
	pxor xmm1, xmm6
	pxor xmm2, xmm6
	pxor xmm3, xmm6
	pxor xmm4, xmm6
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	cmp ecx, 10
	je 23f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	cmp ecx, 12
	je 25f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
	jmp 26f
25:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
26:
	jmp 24f
23:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
24:
	movdqu XMMWORD PTR [edx], xmm0
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu XMMWORD PTR [edx+80], xmm5
	add edx, 96
	mov eax, DWORD PTR [esp+12]
	mov ecx, edx
	sub ecx, eax
	shr ecx, 4
	add ecx, 5
	mov eax, DWORD PTR [esp+16]
	cmp ecx, eax
	mov ecx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	jb 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+12]
	mov ecx, edx
	sub ecx, eax
	shr ecx, 4
	add ecx, 0
	mov eax, DWORD PTR [esp+16]
	cmp ecx, eax
	mov ecx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	jae 27f
29:
	movdqu xmm0, XMMWORD PTR [edx]
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm0, xmm6
	cmp ecx, 10
	je 210f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	cmp ecx, 12
	je 212f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	jmp 213f
212:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
213:
	jmp 211f
210:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
211:
	movdqu XMMWORD PTR [edx], xmm0
	add edx, 16
	mov eax, DWORD PTR [esp+12]
	mov ecx, edx
	sub ecx, eax
	shr ecx, 4
	add ecx, 0
	mov eax, DWORD PTR [esp+16]
	cmp ecx, eax
	mov ecx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	jb 29b
	jmp 28f
27:
28:
	ret
	.p2align 6

vg_aes_ecb_decrypt_aesni:
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
	call {vg_aes_decrypt_blocks_aesni}
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+24], edx
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp], eax
	mov eax, 240
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize}
	mov eax, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
	lea esp, [esp+28]
	ret
	.p2align 6

vg_aes_ecb_encrypt:
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
	call {vg_aes_encrypt_blocks}
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+24], edx
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp], eax
	mov eax, 2048
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize}
	mov eax, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
	lea esp, [esp+28]
	ret
	.p2align 6

vg_aes_ecb_decrypt:
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
	call {vg_aes_decrypt_blocks}
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+24], edx
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp], eax
	mov eax, 2048
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize}
	mov eax, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
	lea esp, [esp+28]
	ret
	.p2align 6
