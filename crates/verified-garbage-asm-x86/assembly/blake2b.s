// The functions of `src/blake2b.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_init:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+16]
	test ecx, ecx
	je 20f
	mov edx, 0
	mov DWORD PTR [eax+64], edx
	mov DWORD PTR [eax+68], edx
	mov DWORD PTR [eax+72], edx
	mov DWORD PTR [eax+76], edx
	mov DWORD PTR [eax+80], edx
	mov DWORD PTR [eax+84], edx
	mov DWORD PTR [eax+88], edx
	mov DWORD PTR [eax+92], edx
	mov DWORD PTR [eax+96], edx
	mov DWORD PTR [eax+100], edx
	mov DWORD PTR [eax+104], edx
	mov DWORD PTR [eax+108], edx
	mov DWORD PTR [eax+112], edx
	mov DWORD PTR [eax+116], edx
	mov DWORD PTR [eax+120], edx
	mov DWORD PTR [eax+124], edx
	mov DWORD PTR [eax+128], edx
	mov DWORD PTR [eax+132], edx
	mov DWORD PTR [eax+136], edx
	mov DWORD PTR [eax+140], edx
	mov DWORD PTR [eax+144], edx
	mov DWORD PTR [eax+148], edx
	mov DWORD PTR [eax+152], edx
	mov DWORD PTR [eax+156], edx
	mov DWORD PTR [eax+160], edx
	mov DWORD PTR [eax+164], edx
	mov DWORD PTR [eax+168], edx
	mov DWORD PTR [eax+172], edx
	mov DWORD PTR [eax+176], edx
	mov DWORD PTR [eax+180], edx
	mov DWORD PTR [eax+184], edx
	mov DWORD PTR [eax+188], edx
	mov DWORD PTR [eax], ebx
	mov edx, DWORD PTR [esp+12]
22:
	movzx ebx, BYTE PTR [edx]
	mov BYTE PTR [eax+64], bl
	add edx, 1
	add eax, 1
	sub ecx, 1
	jne 22b
	mov eax, DWORD PTR [esp+4]
	mov ebx, DWORD PTR [eax]
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+4]
	mov ecx, -205731576
	mov DWORD PTR [eax], ecx
	mov ecx, 1779033703
	mov DWORD PTR [eax+4], ecx
	mov ecx, -2067093701
	mov DWORD PTR [eax+8], ecx
	mov ecx, -1150833019
	mov DWORD PTR [eax+12], ecx
	mov ecx, -23791573
	mov DWORD PTR [eax+16], ecx
	mov ecx, 1013904242
	mov DWORD PTR [eax+20], ecx
	mov ecx, 1595750129
	mov DWORD PTR [eax+24], ecx
	mov ecx, -1521486534
	mov DWORD PTR [eax+28], ecx
	mov ecx, -1377402159
	mov DWORD PTR [eax+32], ecx
	mov ecx, 1359893119
	mov DWORD PTR [eax+36], ecx
	mov ecx, 725511199
	mov DWORD PTR [eax+40], ecx
	mov ecx, -1694144372
	mov DWORD PTR [eax+44], ecx
	mov ecx, -79577749
	mov DWORD PTR [eax+48], ecx
	mov ecx, 528734635
	mov DWORD PTR [eax+52], ecx
	mov ecx, 327033209
	mov DWORD PTR [eax+56], ecx
	mov ecx, 1541459225
	mov DWORD PTR [eax+60], ecx
	mov ecx, DWORD PTR [eax]
	xor ecx, 16842752
	mov edx, DWORD PTR [esp+16]
	ror edx, 24
	xor ecx, edx
	xor ecx, DWORD PTR [esp+8]
	mov DWORD PTR [eax], ecx
	ret
	.p2align 6

vg_blake2b_update:
	lea esp, [esp-604]
	mov eax, DWORD PTR [esp+608]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+612]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+616]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+620]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+624]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+528], eax
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+532], ecx
	or ecx, eax
	je 20f
	sub eax, 1
	and eax, 127
	add eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	test edi, edi
	je 22f
	test eax, eax
	je 24f
	mov ecx, 128
	sub ecx, eax
	cmp edi, ecx
	jb 26f
	jmp 27f
26:
	mov ecx, edi
27:
	sub edi, ecx
	mov edx, ebx
	add edx, eax
	mov eax, DWORD PTR [ebp+528]
	add eax, ecx
	mov DWORD PTR [ebp+528], eax
	mov eax, DWORD PTR [ebp+532]
	adc eax, 0
	mov DWORD PTR [ebp+532], eax
	test ecx, ecx
	je 28f
210:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edx+64], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 210b
	jmp 29f
28:
29:
	test edi, edi
	je 211f
	mov DWORD PTR [ebp+536], esi
	mov DWORD PTR [ebp+540], edi
	mov esi, ebx
	add esi, 64
	mov edi, 1
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	mov eax, 0
	push ebp
	push eax
	push edx
	push ecx
	push edi
	push esi
	push ebx
	call {vg_blake2b_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [ebp+536]
	mov edi, DWORD PTR [ebp+540]
	jmp 212f
211:
212:
	jmp 25f
24:
25:
	test edi, edi
	je 213f
	mov eax, edi
	sub eax, 1
	mov ecx, eax
	and ecx, 127
	sub eax, ecx
	je 215f
	mov DWORD PTR [ebp+540], edi
	mov DWORD PTR [ebp+544], eax
	mov edi, eax
	shr edi, 7
	mov ecx, DWORD PTR [ebp+528]
	add ecx, 128
	mov edx, DWORD PTR [ebp+532]
	adc edx, 0
	mov eax, 0
	push ebp
	push eax
	push edx
	push ecx
	push edi
	push esi
	push ebx
	call {vg_blake2b_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+544]
	add esi, eax
	mov edi, DWORD PTR [ebp+540]
	sub edi, eax
	jmp 216f
215:
216:
	mov ecx, edi
	mov edx, ebx
217:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edx+64], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 217b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov eax, ebp
	mov ebx, DWORD PTR [eax+512]
	mov esi, DWORD PTR [eax+516]
	mov edi, DWORD PTR [eax+520]
	mov ebp, DWORD PTR [eax+524]
	lea esp, [esp+604]
	ret
	.p2align 6

vg_blake2b_finalize:
	lea esp, [esp-600]
	mov eax, DWORD PTR [esp+604]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+608]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+612]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+616]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	or ecx, eax
	je 20f
	sub eax, 1
	and eax, 127
	add eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	mov edx, ebx
	add edx, eax
	mov ecx, 128
	sub ecx, eax
	mov eax, 0
	je 22f
24:
	mov BYTE PTR [edx+64], al
	add edx, 1
	sub ecx, 1
	jne 24b
	jmp 23f
22:
23:
	mov esi, ebx
	add esi, 64
	mov edi, 1
	mov eax, 1
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	push ebp
	push eax
	push edx
	push ecx
	push edi
	push esi
	push ebx
	call {vg_blake2b_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [ebx]
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	mov DWORD PTR [eax+28], ecx
	mov ecx, DWORD PTR [ebx+32]
	mov DWORD PTR [eax+32], ecx
	mov ecx, DWORD PTR [ebx+36]
	mov DWORD PTR [eax+36], ecx
	mov ecx, DWORD PTR [ebx+40]
	mov DWORD PTR [eax+40], ecx
	mov ecx, DWORD PTR [ebx+44]
	mov DWORD PTR [eax+44], ecx
	mov ecx, DWORD PTR [ebx+48]
	mov DWORD PTR [eax+48], ecx
	mov ecx, DWORD PTR [ebx+52]
	mov DWORD PTR [eax+52], ecx
	mov ecx, DWORD PTR [ebx+56]
	mov DWORD PTR [eax+56], ecx
	mov ecx, DWORD PTR [ebx+60]
	mov DWORD PTR [eax+60], ecx
	mov eax, ebp
	mov ebx, DWORD PTR [eax+512]
	mov esi, DWORD PTR [eax+516]
	mov edi, DWORD PTR [eax+520]
	mov ebp, DWORD PTR [eax+524]
	lea esp, [esp+600]
	ret
	.p2align 6
