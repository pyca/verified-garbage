// The functions of `src/internal/vg_chacha20_poly1305_seal_core.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_seal_core:
	lea esp, [esp-884]
	mov eax, DWORD PTR [esp+888]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+892]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+896]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+900]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+904]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+908]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+912]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov ecx, DWORD PTR [esp+20]
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+8]
	mov eax, 1634760805
	mov DWORD PTR [edi+64], eax
	mov eax, 857760878
	mov DWORD PTR [edi+68], eax
	mov eax, 2036477234
	mov DWORD PTR [edi+72], eax
	mov eax, 1797285236
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [ecx+16]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [ecx+20]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [ecx+24]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [ecx+28]
	mov DWORD PTR [edi+108], eax
	mov eax, 0
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [edi+124], eax
	mov ecx, edi
	add ecx, 64
	mov edx, edi
	add edx, 128
	mov eax, DWORD PTR [esp+24]
	sub eax, 1
	cmp eax, 192
	jb 20f
	push edx
	push ecx
	call {vg_chacha20_block}
	pop eax
	pop eax
	mov ecx, edi
	add ecx, 128
	mov edx, edi
	add edx, 448
	push ecx
	push edx
	call {vg_poly1305_init_core}
	pop eax
	pop eax
	jmp 21f
20:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [edi+576], xmm0
	movdqu XMMWORD PTR [edi+592], xmm0
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu XMMWORD PTR [edi+640], xmm0
	movdqu XMMWORD PTR [edi+656], xmm0
	movdqu XMMWORD PTR [edi+672], xmm0
	movdqu XMMWORD PTR [edi+688], xmm0
	movdqu XMMWORD PTR [edi+704], xmm0
	movdqu XMMWORD PTR [edi+720], xmm0
	movdqu XMMWORD PTR [edi+736], xmm0
	movdqu XMMWORD PTR [edi+752], xmm0
	movdqu XMMWORD PTR [edi+768], xmm0
	movdqu XMMWORD PTR [edi+784], xmm0
	movdqu XMMWORD PTR [edi+800], xmm0
	movdqu XMMWORD PTR [edi+816], xmm0
	mov eax, edi
	add eax, 64
	mov ecx, edi
	add ecx, 576
	mov edx, 256
	mov ebx, edi
	add ebx, 128
	mov esi, ecx
	push ebx
	push edx
	push ecx
	push eax
	call {vg_chacha20_xor}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, edi
	add ecx, 576
	mov edx, edi
	add edx, 448
	push ecx
	push edx
	call {vg_poly1305_init_core}
	pop eax
	pop eax
21:
	mov ebx, DWORD PTR [esp+12]
	mov ebp, DWORD PTR [esp+16]
	mov eax, ebp
	shr eax, 4
	mov ecx, edi
	add ecx, 448
	push eax
	push ebx
	push ecx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	and edx, 15
	je 22f
	mov esi, ebp
	sub esi, edx
	add esi, ebx
	mov eax, 0
	mov DWORD PTR [edi+48], eax
	mov DWORD PTR [edi+52], eax
	mov DWORD PTR [edi+56], eax
	mov DWORD PTR [edi+60], eax
	mov ecx, edi
	add ecx, 48
24:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ecx], al
	add esi, 1
	add ecx, 1
	sub edx, 1
	jne 24b
	mov eax, 1
	mov ecx, edi
	add ecx, 48
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	jmp 23f
22:
23:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [edi+40], eax
	mov eax, 0
	mov DWORD PTR [edi+36], eax
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [esp+24]
	sub eax, 1
	cmp eax, 192
	jb 25f
	mov eax, 1
	mov DWORD PTR [edi+112], eax
	mov eax, edi
	add eax, 64
	mov ecx, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
	mov ebx, edi
	add ebx, 128
	mov esi, DWORD PTR [esp+32]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_chacha20_xor}
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 26f
25:
	mov esi, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+32]
	mov ecx, DWORD PTR [esp+24]
	mov ebp, edi
	add ebp, 640
	cmp ecx, 16
	jb 27f
29:
	movdqu xmm4, XMMWORD PTR [esi]
	movdqu xmm5, XMMWORD PTR [ebp]
	pxor xmm4, xmm5
	movdqu XMMWORD PTR [edx], xmm4
	add esi, 16
	add edx, 16
	add ebp, 16
	sub ecx, 16
	cmp ecx, 16
	jae 29b
	jmp 28f
27:
28:
	test ecx, ecx
	je 210f
212:
	movzx eax, BYTE PTR [esi]
	xor eax, DWORD PTR [ebp]
	mov BYTE PTR [edx], al
	add esi, 1
	add edx, 1
	add ebp, 1
	sub ecx, 1
	jne 212b
	jmp 211f
210:
211:
26:
	mov ebx, DWORD PTR [esp+20]
	mov ebp, DWORD PTR [esp+24]
	mov eax, ebp
	shr eax, 4
	mov ecx, edi
	add ecx, 448
	push eax
	push ebx
	push ecx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	and edx, 15
	je 213f
	mov esi, ebp
	sub esi, edx
	add esi, ebx
	mov eax, 0
	mov DWORD PTR [edi+48], eax
	mov DWORD PTR [edi+52], eax
	mov DWORD PTR [edi+56], eax
	mov DWORD PTR [edi+60], eax
	mov ecx, edi
	add ecx, 48
215:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ecx], al
	add esi, 1
	add ecx, 1
	sub edx, 1
	jne 215b
	mov eax, 1
	mov ecx, edi
	add ecx, 48
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	jmp 214f
213:
214:
	mov eax, 1
	mov ecx, edi
	add ecx, 32
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov ebx, edi
	add ebx, 576
	mov ecx, DWORD PTR [esp+28]
	mov eax, 0
	mov esi, edi
	add esi, 448
	push ebx
	push ecx
	push eax
	push eax
	push esi
	call {vg_poly1305_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [edi]
	mov esi, DWORD PTR [edi+4]
	mov ebp, DWORD PTR [edi+12]
	mov edi, DWORD PTR [edi+8]
	lea esp, [esp+884]
	ret
	.p2align 6
