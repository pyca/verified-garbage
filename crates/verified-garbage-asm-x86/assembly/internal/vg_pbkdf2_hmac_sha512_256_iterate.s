// The functions of `src/internal/vg_pbkdf2_hmac_sha512_256_iterate.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha512_256_iterate:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+272], ebx
	mov DWORD PTR [eax+276], esi
	mov DWORD PTR [eax+280], edi
	mov DWORD PTR [eax+284], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+4]
	mov edi, DWORD PTR [esp+12]
	mov ebx, ebp
	add ebx, 288
	mov edx, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [edx]
	mov DWORD PTR [ebx+64], ecx
	mov ecx, DWORD PTR [edx+4]
	mov DWORD PTR [ebx+68], ecx
	mov ecx, DWORD PTR [edx+8]
	mov DWORD PTR [ebx+72], ecx
	mov ecx, DWORD PTR [edx+12]
	mov DWORD PTR [ebx+76], ecx
	mov ecx, DWORD PTR [edx+16]
	mov DWORD PTR [ebx+80], ecx
	mov ecx, DWORD PTR [edx+20]
	mov DWORD PTR [ebx+84], ecx
	mov ecx, DWORD PTR [edx+24]
	mov DWORD PTR [ebx+88], ecx
	mov ecx, DWORD PTR [edx+28]
	mov DWORD PTR [ebx+92], ecx
	mov ecx, 128
	mov DWORD PTR [ebx+96], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+100], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+104], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+108], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+112], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+116], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+120], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+124], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+128], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+132], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+136], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+140], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+144], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+148], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+152], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+156], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+160], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+164], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+168], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+172], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+176], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+180], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+184], ecx
	mov ecx, 327680
	mov DWORD PTR [ebx+188], ecx
	test edi, edi
	je 20f
22:
	mov ecx, DWORD PTR [esi]
	mov DWORD PTR [ebx], ecx
	mov ecx, DWORD PTR [esi+4]
	mov DWORD PTR [ebx+4], ecx
	mov ecx, DWORD PTR [esi+8]
	mov DWORD PTR [ebx+8], ecx
	mov ecx, DWORD PTR [esi+12]
	mov DWORD PTR [ebx+12], ecx
	mov ecx, DWORD PTR [esi+16]
	mov DWORD PTR [ebx+16], ecx
	mov ecx, DWORD PTR [esi+20]
	mov DWORD PTR [ebx+20], ecx
	mov ecx, DWORD PTR [esi+24]
	mov DWORD PTR [ebx+24], ecx
	mov ecx, DWORD PTR [esi+28]
	mov DWORD PTR [ebx+28], ecx
	mov ecx, DWORD PTR [esi+32]
	mov DWORD PTR [ebx+32], ecx
	mov ecx, DWORD PTR [esi+36]
	mov DWORD PTR [ebx+36], ecx
	mov ecx, DWORD PTR [esi+40]
	mov DWORD PTR [ebx+40], ecx
	mov ecx, DWORD PTR [esi+44]
	mov DWORD PTR [ebx+44], ecx
	mov ecx, DWORD PTR [esi+48]
	mov DWORD PTR [ebx+48], ecx
	mov ecx, DWORD PTR [esi+52]
	mov DWORD PTR [ebx+52], ecx
	mov ecx, DWORD PTR [esi+56]
	mov DWORD PTR [ebx+56], ecx
	mov ecx, DWORD PTR [esi+60]
	mov DWORD PTR [ebx+60], ecx
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebx
	add eax, 64
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov ecx, DWORD PTR [ebx+36]
	bswap ecx
	mov DWORD PTR [eax+32], ecx
	mov ecx, DWORD PTR [ebx+32]
	bswap ecx
	mov DWORD PTR [eax+36], ecx
	mov ecx, DWORD PTR [ebx+44]
	bswap ecx
	mov DWORD PTR [eax+40], ecx
	mov ecx, DWORD PTR [ebx+40]
	bswap ecx
	mov DWORD PTR [eax+44], ecx
	mov ecx, DWORD PTR [ebx+52]
	bswap ecx
	mov DWORD PTR [eax+48], ecx
	mov ecx, DWORD PTR [ebx+48]
	bswap ecx
	mov DWORD PTR [eax+52], ecx
	mov ecx, DWORD PTR [ebx+60]
	bswap ecx
	mov DWORD PTR [eax+56], ecx
	mov ecx, DWORD PTR [ebx+56]
	bswap ecx
	mov DWORD PTR [eax+60], ecx
	mov ecx, 128
	mov DWORD PTR [ebx+96], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+100], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+104], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+108], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+112], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+116], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+120], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+124], ecx
	mov ecx, DWORD PTR [esi+192]
	mov DWORD PTR [ebx], ecx
	mov ecx, DWORD PTR [esi+196]
	mov DWORD PTR [ebx+4], ecx
	mov ecx, DWORD PTR [esi+200]
	mov DWORD PTR [ebx+8], ecx
	mov ecx, DWORD PTR [esi+204]
	mov DWORD PTR [ebx+12], ecx
	mov ecx, DWORD PTR [esi+208]
	mov DWORD PTR [ebx+16], ecx
	mov ecx, DWORD PTR [esi+212]
	mov DWORD PTR [ebx+20], ecx
	mov ecx, DWORD PTR [esi+216]
	mov DWORD PTR [ebx+24], ecx
	mov ecx, DWORD PTR [esi+220]
	mov DWORD PTR [ebx+28], ecx
	mov ecx, DWORD PTR [esi+224]
	mov DWORD PTR [ebx+32], ecx
	mov ecx, DWORD PTR [esi+228]
	mov DWORD PTR [ebx+36], ecx
	mov ecx, DWORD PTR [esi+232]
	mov DWORD PTR [ebx+40], ecx
	mov ecx, DWORD PTR [esi+236]
	mov DWORD PTR [ebx+44], ecx
	mov ecx, DWORD PTR [esi+240]
	mov DWORD PTR [ebx+48], ecx
	mov ecx, DWORD PTR [esi+244]
	mov DWORD PTR [ebx+52], ecx
	mov ecx, DWORD PTR [esi+248]
	mov DWORD PTR [ebx+56], ecx
	mov ecx, DWORD PTR [esi+252]
	mov DWORD PTR [ebx+60], ecx
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebx
	add eax, 64
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov ecx, DWORD PTR [ebx+36]
	bswap ecx
	mov DWORD PTR [eax+32], ecx
	mov ecx, DWORD PTR [ebx+32]
	bswap ecx
	mov DWORD PTR [eax+36], ecx
	mov ecx, DWORD PTR [ebx+44]
	bswap ecx
	mov DWORD PTR [eax+40], ecx
	mov ecx, DWORD PTR [ebx+40]
	bswap ecx
	mov DWORD PTR [eax+44], ecx
	mov ecx, DWORD PTR [ebx+52]
	bswap ecx
	mov DWORD PTR [eax+48], ecx
	mov ecx, DWORD PTR [ebx+48]
	bswap ecx
	mov DWORD PTR [eax+52], ecx
	mov ecx, DWORD PTR [ebx+60]
	bswap ecx
	mov DWORD PTR [eax+56], ecx
	mov ecx, DWORD PTR [ebx+56]
	bswap ecx
	mov DWORD PTR [eax+60], ecx
	mov ecx, 128
	mov DWORD PTR [ebx+96], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+100], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+104], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+108], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+112], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+116], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+120], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+124], ecx
	mov edx, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [ebx+64]
	xor ecx, DWORD PTR [edx]
	mov DWORD PTR [edx], ecx
	mov ecx, DWORD PTR [ebx+68]
	xor ecx, DWORD PTR [edx+4]
	mov DWORD PTR [edx+4], ecx
	mov ecx, DWORD PTR [ebx+72]
	xor ecx, DWORD PTR [edx+8]
	mov DWORD PTR [edx+8], ecx
	mov ecx, DWORD PTR [ebx+76]
	xor ecx, DWORD PTR [edx+12]
	mov DWORD PTR [edx+12], ecx
	mov ecx, DWORD PTR [ebx+80]
	xor ecx, DWORD PTR [edx+16]
	mov DWORD PTR [edx+16], ecx
	mov ecx, DWORD PTR [ebx+84]
	xor ecx, DWORD PTR [edx+20]
	mov DWORD PTR [edx+20], ecx
	mov ecx, DWORD PTR [ebx+88]
	xor ecx, DWORD PTR [edx+24]
	mov DWORD PTR [edx+24], ecx
	mov ecx, DWORD PTR [ebx+92]
	xor ecx, DWORD PTR [edx+28]
	mov DWORD PTR [edx+28], ecx
	sub edi, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, ebp
	mov ebx, DWORD PTR [eax+272]
	mov esi, DWORD PTR [eax+276]
	mov edi, DWORD PTR [eax+280]
	mov ebp, DWORD PTR [eax+284]
	ret
	.p2align 6
