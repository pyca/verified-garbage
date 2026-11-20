// The functions of `src/internal/vg_chacha20_poly1305_seal_core_ssse3.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_seal_core_ssse3:
	lea esp, [esp-740]
	mov eax, DWORD PTR [esp+744]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+748]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+752]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+756]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+760]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+764]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+768]
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
	je 20f
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
22:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ecx], al
	add esi, 1
	add ecx, 1
	sub edx, 1
	jne 22b
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
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [edi+40], eax
	mov eax, 0
	mov DWORD PTR [edi+36], eax
	mov DWORD PTR [edi+44], eax
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
	call {vg_chacha20_xor_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
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
	je 23f
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
25:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ecx], al
	add esi, 1
	add ecx, 1
	sub edx, 1
	jne 25b
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
	jmp 24f
23:
24:
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
	lea esp, [esp+740]
	ret
	.p2align 6
