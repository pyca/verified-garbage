// The functions of `src/chacha20.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_init:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	movdqu xmm1, XMMWORD PTR [ecx]
	movdqu xmm2, XMMWORD PTR [ecx+16]
	mov edx, DWORD PTR [esp+12]
	movdqu xmm0, XMMWORD PTR [edx]
	mov ecx, 0
	sub ecx, DWORD PTR [edx]
	mov edx, 1
	sbb edx, 0
	add ecx, ecx
	adc edx, edx
	add ecx, ecx
	adc edx, edx
	add ecx, ecx
	adc edx, edx
	add ecx, ecx
	adc edx, edx
	add ecx, ecx
	adc edx, edx
	add ecx, ecx
	adc edx, edx
	movdqu XMMWORD PTR [eax+16], xmm1
	movdqu XMMWORD PTR [eax+32], xmm2
	movdqu XMMWORD PTR [eax+48], xmm0
	mov DWORD PTR [eax+128], ecx
	mov DWORD PTR [eax+132], edx
	mov ecx, 1634760805
	mov DWORD PTR [eax], ecx
	mov ecx, 857760878
	mov DWORD PTR [eax+4], ecx
	mov ecx, 2036477234
	mov DWORD PTR [eax+8], ecx
	mov ecx, 1797285236
	mov DWORD PTR [eax+12], ecx
	ret
	.p2align 6

vg_chacha20_set_nonce:
	mov eax, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+8]
	movdqu xmm0, XMMWORD PTR [edx]
	mov ecx, 0
	sub ecx, DWORD PTR [edx]
	mov edx, 1
	sbb edx, 0
	add ecx, ecx
	adc edx, edx
	add ecx, ecx
	adc edx, edx
	add ecx, ecx
	adc edx, edx
	add ecx, ecx
	adc edx, edx
	add ecx, ecx
	adc edx, edx
	add ecx, ecx
	adc edx, edx
	movdqu XMMWORD PTR [eax+48], xmm0
	mov DWORD PTR [eax+128], ecx
	mov DWORD PTR [eax+132], edx
	mov ecx, 1634760805
	mov DWORD PTR [eax], ecx
	mov ecx, 857760878
	mov DWORD PTR [eax+4], ecx
	mov ecx, 2036477234
	mov DWORD PTR [eax+8], ecx
	mov ecx, 1797285236
	mov DWORD PTR [eax+12], ecx
	ret
	.p2align 6

vg_chacha20_apply:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [eax+128]
	mov edx, DWORD PTR [eax+132]
	sub ecx, DWORD PTR [esp+12]
	sbb edx, 0
	jb 20f
	mov DWORD PTR [eax+576], ebx
	mov DWORD PTR [eax+580], esi
	mov DWORD PTR [eax+584], edi
	mov DWORD PTR [eax+588], ebp
	mov DWORD PTR [eax+600], ecx
	mov DWORD PTR [eax+604], edx
	mov ebx, eax
	mov esi, DWORD PTR [esp+8]
	mov ebp, DWORD PTR [esp+12]
	mov eax, DWORD PTR [ebx+128]
	and eax, 63
	mov ecx, ebp
	cmp eax, ebp
	jb 22f
	jmp 23f
22:
	mov ecx, eax
23:
	mov edx, ebx
	add edx, 128
	sub edx, eax
	sub ebp, ecx
	test ecx, ecx
	je 24f
26:
	movzx eax, BYTE PTR [esi]
	xor eax, DWORD PTR [edx]
	mov BYTE PTR [esi], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 26b
	jmp 25f
24:
25:
	mov ecx, ebp
	and ecx, -64
	je 27f
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebx+16]
	movdqu xmm2, XMMWORD PTR [ebx+32]
	movdqu xmm3, XMMWORD PTR [ebx+48]
	movdqu XMMWORD PTR [ebx+192], xmm0
	movdqu XMMWORD PTR [ebx+208], xmm1
	movdqu XMMWORD PTR [ebx+224], xmm2
	movdqu XMMWORD PTR [ebx+240], xmm3
	mov eax, ecx
	shr eax, 6
	add eax, DWORD PTR [ebx+48]
	mov DWORD PTR [ebx+48], eax
	mov edi, ecx
	mov eax, ebx
	add eax, 256
	mov edx, ebx
	add edx, 192
	push eax
	push ecx
	push esi
	push edx
	call {vg_chacha20_xor}
	pop eax
	pop eax
	pop eax
	pop eax
	add esi, edi
	sub ebp, edi
	jmp 28f
27:
28:
	test ebp, ebp
	je 29f
	mov eax, ebx
	add eax, 64
	push eax
	push ebx
	call {vg_chacha20_block}
	pop eax
	pop eax
	mov eax, DWORD PTR [ebx+48]
	add eax, 1
	mov DWORD PTR [ebx+48], eax
	mov edx, ebx
	add edx, 64
	mov ecx, ebp
	test ecx, ecx
	je 211f
213:
	movzx eax, BYTE PTR [esi]
	xor eax, DWORD PTR [edx]
	mov BYTE PTR [esi], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	jmp 212f
211:
212:
	jmp 210f
29:
210:
	mov eax, DWORD PTR [ebx+600]
	mov DWORD PTR [ebx+128], eax
	mov eax, DWORD PTR [ebx+604]
	mov DWORD PTR [ebx+132], eax
	mov esi, DWORD PTR [ebx+580]
	mov edi, DWORD PTR [ebx+584]
	mov ebp, DWORD PTR [ebx+588]
	mov ebx, DWORD PTR [ebx+576]
	mov eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	ret
	.p2align 6

vg_chacha20_apply_ssse3:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [eax+128]
	mov edx, DWORD PTR [eax+132]
	sub ecx, DWORD PTR [esp+12]
	sbb edx, 0
	jb 20f
	mov DWORD PTR [eax+576], ebx
	mov DWORD PTR [eax+580], esi
	mov DWORD PTR [eax+584], edi
	mov DWORD PTR [eax+588], ebp
	mov DWORD PTR [eax+600], ecx
	mov DWORD PTR [eax+604], edx
	mov ebx, eax
	mov esi, DWORD PTR [esp+8]
	mov ebp, DWORD PTR [esp+12]
	mov eax, DWORD PTR [ebx+128]
	and eax, 63
	mov ecx, ebp
	cmp eax, ebp
	jb 22f
	jmp 23f
22:
	mov ecx, eax
23:
	mov edx, ebx
	add edx, 128
	sub edx, eax
	sub ebp, ecx
	test ecx, ecx
	je 24f
26:
	movzx eax, BYTE PTR [esi]
	xor eax, DWORD PTR [edx]
	mov BYTE PTR [esi], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 26b
	jmp 25f
24:
25:
	mov ecx, ebp
	and ecx, -64
	je 27f
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebx+16]
	movdqu xmm2, XMMWORD PTR [ebx+32]
	movdqu xmm3, XMMWORD PTR [ebx+48]
	movdqu XMMWORD PTR [ebx+192], xmm0
	movdqu XMMWORD PTR [ebx+208], xmm1
	movdqu XMMWORD PTR [ebx+224], xmm2
	movdqu XMMWORD PTR [ebx+240], xmm3
	mov eax, ecx
	shr eax, 6
	add eax, DWORD PTR [ebx+48]
	mov DWORD PTR [ebx+48], eax
	mov edi, ecx
	mov eax, ebx
	add eax, 256
	mov edx, ebx
	add edx, 192
	push eax
	push ecx
	push esi
	push edx
	call {vg_chacha20_xor_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	add esi, edi
	sub ebp, edi
	jmp 28f
27:
28:
	test ebp, ebp
	je 29f
	mov eax, ebx
	add eax, 64
	push eax
	push ebx
	call {vg_chacha20_block}
	pop eax
	pop eax
	mov eax, DWORD PTR [ebx+48]
	add eax, 1
	mov DWORD PTR [ebx+48], eax
	mov edx, ebx
	add edx, 64
	mov ecx, ebp
	test ecx, ecx
	je 211f
213:
	movzx eax, BYTE PTR [esi]
	xor eax, DWORD PTR [edx]
	mov BYTE PTR [esi], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	jmp 212f
211:
212:
	jmp 210f
29:
210:
	mov eax, DWORD PTR [ebx+600]
	mov DWORD PTR [ebx+128], eax
	mov eax, DWORD PTR [ebx+604]
	mov DWORD PTR [ebx+132], eax
	mov esi, DWORD PTR [ebx+580]
	mov edi, DWORD PTR [ebx+584]
	mov ebp, DWORD PTR [ebx+588]
	mov ebx, DWORD PTR [ebx+576]
	mov eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	ret
	.p2align 6
