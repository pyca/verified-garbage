// The functions of `src/rc2.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_init:
	lea esp, [esp-608]
	mov eax, DWORD PTR [esp+612]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+616]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+620]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+624]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+628]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+632]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, 1
	mov ecx, DWORD PTR [esp+8]
	sub ecx, 1
	cmp ecx, 128
	jae 20f
	mov eax, 2
	mov ecx, DWORD PTR [esp+12]
	sub ecx, 1
	cmp ecx, 1024
	jae 22f
	mov eax, 3
	mov ecx, DWORD PTR [esp+20]
	cmp ecx, 8
	jne 24f
	mov eax, 0
	jmp 25f
24:
25:
	jmp 23f
22:
23:
	jmp 21f
20:
21:
	test eax, eax
	jne 26f
	mov eax, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [esp+24]
	mov edx, DWORD PTR [eax]
	mov DWORD PTR [ecx+128], edx
	mov edx, DWORD PTR [eax+4]
	mov DWORD PTR [ecx+132], edx
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov ebx, eax
	mov esi, ecx
	mov edx, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	push ebx
	push esi
	push edx
	push ecx
	push eax
	call {vg_rc2_expand_key}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [ebx+516]
	mov ebx, DWORD PTR [ebx+512]
	mov eax, 0
	jmp 27f
26:
27:
	lea esp, [esp+608]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-632]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	movdqu XMMWORD PTR [esp+112], xmm0
	movdqu XMMWORD PTR [esp+128], xmm0
	movdqu XMMWORD PTR [esp+144], xmm0
	movdqu XMMWORD PTR [esp+160], xmm0
	movdqu XMMWORD PTR [esp+176], xmm0
	movdqu XMMWORD PTR [esp+192], xmm0
	movdqu XMMWORD PTR [esp+208], xmm0
	movdqu XMMWORD PTR [esp+224], xmm0
	movdqu XMMWORD PTR [esp+240], xmm0
	movdqu XMMWORD PTR [esp+256], xmm0
	movdqu XMMWORD PTR [esp+272], xmm0
	movdqu XMMWORD PTR [esp+288], xmm0
	movdqu XMMWORD PTR [esp+304], xmm0
	movdqu XMMWORD PTR [esp+320], xmm0
	movdqu XMMWORD PTR [esp+336], xmm0
	movdqu XMMWORD PTR [esp+352], xmm0
	movdqu XMMWORD PTR [esp+368], xmm0
	movdqu XMMWORD PTR [esp+384], xmm0
	movdqu XMMWORD PTR [esp+400], xmm0
	movdqu XMMWORD PTR [esp+416], xmm0
	movdqu XMMWORD PTR [esp+432], xmm0
	movdqu XMMWORD PTR [esp+448], xmm0
	movdqu XMMWORD PTR [esp+464], xmm0
	movdqu XMMWORD PTR [esp+480], xmm0
	movdqu XMMWORD PTR [esp+496], xmm0
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	movdqu XMMWORD PTR [esp+608], xmm0
	mov DWORD PTR [esp+624], ecx
	mov DWORD PTR [esp+628], ecx
	lea esp, [esp+632]
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
