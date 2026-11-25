// The functions of `src/internal/vg_ghash.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ghash:
	mov ecx, DWORD PTR [esp+20]
	mov DWORD PTR [ecx+224], ebx
	mov DWORD PTR [ecx+228], esi
	mov DWORD PTR [ecx+232], edi
	mov DWORD PTR [ecx+236], ebp
	mov edx, DWORD PTR [esp+12]
	mov DWORD PTR [ecx+240], edx
	mov edx, DWORD PTR [esp+16]
	mov DWORD PTR [ecx+244], edx
	mov edx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edx]
	mov ebx, DWORD PTR [edx+4]
	mov esi, DWORD PTR [edx+8]
	mov edi, DWORD PTR [edx+12]
	bswap eax
	bswap ebx
	bswap esi
	bswap edi
	mov ebp, eax
	shr ebp, 31
	add eax, eax
	mov edx, ebx
	shr edx, 31
	xor eax, edx
	add ebx, ebx
	mov edx, esi
	shr edx, 31
	xor ebx, edx
	add esi, esi
	mov edx, edi
	shr edx, 31
	xor esi, edx
	add edi, edi
	xor edi, ebp
	ror ebp, 1
	xor eax, ebp
	ror ebp, 1
	xor eax, ebp
	ror ebp, 5
	xor eax, ebp
	mov edx, edi
	and edx, 286331153
	mov DWORD PTR [ecx], edx
	mov edx, edi
	and edx, 572662306
	mov DWORD PTR [ecx+4], edx
	mov edx, edi
	and edx, 1145324612
	mov DWORD PTR [ecx+8], edx
	mov edx, edi
	and edx, -2004318072
	mov DWORD PTR [ecx+12], edx
	mov edx, esi
	and edx, 286331153
	mov DWORD PTR [ecx+16], edx
	mov edx, esi
	and edx, 572662306
	mov DWORD PTR [ecx+20], edx
	mov edx, esi
	and edx, 1145324612
	mov DWORD PTR [ecx+24], edx
	mov edx, esi
	and edx, -2004318072
	mov DWORD PTR [ecx+28], edx
	mov ebp, edi
	xor ebp, esi
	mov edx, ebp
	and edx, 286331153
	mov DWORD PTR [ecx+32], edx
	mov edx, ebp
	and edx, 572662306
	mov DWORD PTR [ecx+36], edx
	mov edx, ebp
	and edx, 1145324612
	mov DWORD PTR [ecx+40], edx
	mov edx, ebp
	and edx, -2004318072
	mov DWORD PTR [ecx+44], edx
	mov edx, ebx
	and edx, 286331153
	mov DWORD PTR [ecx+48], edx
	mov edx, ebx
	and edx, 572662306
	mov DWORD PTR [ecx+52], edx
	mov edx, ebx
	and edx, 1145324612
	mov DWORD PTR [ecx+56], edx
	mov edx, ebx
	and edx, -2004318072
	mov DWORD PTR [ecx+60], edx
	mov edx, eax
	and edx, 286331153
	mov DWORD PTR [ecx+64], edx
	mov edx, eax
	and edx, 572662306
	mov DWORD PTR [ecx+68], edx
	mov edx, eax
	and edx, 1145324612
	mov DWORD PTR [ecx+72], edx
	mov edx, eax
	and edx, -2004318072
	mov DWORD PTR [ecx+76], edx
	mov ebp, ebx
	xor ebp, eax
	mov edx, ebp
	and edx, 286331153
	mov DWORD PTR [ecx+80], edx
	mov edx, ebp
	and edx, 572662306
	mov DWORD PTR [ecx+84], edx
	mov edx, ebp
	and edx, 1145324612
	mov DWORD PTR [ecx+88], edx
	mov edx, ebp
	and edx, -2004318072
	mov DWORD PTR [ecx+92], edx
	mov ebp, edi
	xor ebp, ebx
	mov edx, ebp
	and edx, 286331153
	mov DWORD PTR [ecx+96], edx
	mov edx, ebp
	and edx, 572662306
	mov DWORD PTR [ecx+100], edx
	mov edx, ebp
	and edx, 1145324612
	mov DWORD PTR [ecx+104], edx
	mov edx, ebp
	and edx, -2004318072
	mov DWORD PTR [ecx+108], edx
	mov edi, ebp
	mov ebp, esi
	xor ebp, eax
	mov edx, ebp
	and edx, 286331153
	mov DWORD PTR [ecx+112], edx
	mov edx, ebp
	and edx, 572662306
	mov DWORD PTR [ecx+116], edx
	mov edx, ebp
	and edx, 1145324612
	mov DWORD PTR [ecx+120], edx
	mov edx, ebp
	and edx, -2004318072
	mov DWORD PTR [ecx+124], edx
	xor ebp, edi
	mov edx, ebp
	and edx, 286331153
	mov DWORD PTR [ecx+128], edx
	mov edx, ebp
	and edx, 572662306
	mov DWORD PTR [ecx+132], edx
	mov edx, ebp
	and edx, 1145324612
	mov DWORD PTR [ecx+136], edx
	mov edx, ebp
	and edx, -2004318072
	mov DWORD PTR [ecx+140], edx
	mov edx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edx]
	mov ebx, DWORD PTR [edx+4]
	mov esi, DWORD PTR [edx+8]
	mov edi, DWORD PTR [edx+12]
	bswap eax
	bswap ebx
	bswap esi
	bswap edi
	mov DWORD PTR [ecx+172], eax
	mov DWORD PTR [ecx+168], ebx
	mov DWORD PTR [ecx+164], esi
	mov DWORD PTR [ecx+160], edi
	mov eax, DWORD PTR [ecx+244]
	test eax, eax
	je 20f
22:
	mov edx, DWORD PTR [ecx+240]
	mov eax, DWORD PTR [edx]
	mov ebx, DWORD PTR [edx+4]
	mov esi, DWORD PTR [edx+8]
	mov edi, DWORD PTR [edx+12]
	add edx, 16
	mov DWORD PTR [ecx+240], edx
	bswap eax
	bswap ebx
	bswap esi
	bswap edi
	xor eax, DWORD PTR [ecx+172]
	xor ebx, DWORD PTR [ecx+168]
	xor esi, DWORD PTR [ecx+164]
	xor edi, DWORD PTR [ecx+160]
	mov DWORD PTR [ecx+172], eax
	mov DWORD PTR [ecx+168], ebx
	mov DWORD PTR [ecx+164], esi
	mov DWORD PTR [ecx+160], edi
	mov eax, DWORD PTR [ecx+160]
	mov edx, eax
	and edx, 286331153
	mov DWORD PTR [ecx+144], edx
	mov edx, eax
	and edx, 572662306
	mov DWORD PTR [ecx+148], edx
	mov edx, eax
	and edx, 1145324612
	mov DWORD PTR [ecx+152], edx
	mov edx, eax
	and edx, -2004318072
	mov DWORD PTR [ecx+156], edx
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+12]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+8]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+4]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 286331153
	and esi, 286331153
	mov edi, ebx
	mov ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+4]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+12]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+8]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 572662306
	and esi, 572662306
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+8]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+4]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+12]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 1145324612
	and esi, 1145324612
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+12]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+8]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+4]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, -2004318072
	and esi, -2004318072
	xor edi, ebx
	xor ebp, esi
	mov DWORD PTR [ecx+176], edi
	mov DWORD PTR [ecx+180], ebp
	mov eax, DWORD PTR [ecx+164]
	mov edx, eax
	and edx, 286331153
	mov DWORD PTR [ecx+144], edx
	mov edx, eax
	and edx, 572662306
	mov DWORD PTR [ecx+148], edx
	mov edx, eax
	and edx, 1145324612
	mov DWORD PTR [ecx+152], edx
	mov edx, eax
	and edx, -2004318072
	mov DWORD PTR [ecx+156], edx
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+16]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+28]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+24]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+20]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 286331153
	and esi, 286331153
	mov edi, ebx
	mov ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+20]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+16]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+28]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+24]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 572662306
	and esi, 572662306
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+24]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+20]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+16]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+28]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 1145324612
	and esi, 1145324612
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+28]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+24]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+20]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+16]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, -2004318072
	and esi, -2004318072
	xor edi, ebx
	xor ebp, esi
	mov DWORD PTR [ecx+184], edi
	mov DWORD PTR [ecx+188], ebp
	mov eax, DWORD PTR [ecx+160]
	xor eax, DWORD PTR [ecx+164]
	mov edx, eax
	and edx, 286331153
	mov DWORD PTR [ecx+144], edx
	mov edx, eax
	and edx, 572662306
	mov DWORD PTR [ecx+148], edx
	mov edx, eax
	and edx, 1145324612
	mov DWORD PTR [ecx+152], edx
	mov edx, eax
	and edx, -2004318072
	mov DWORD PTR [ecx+156], edx
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+32]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+44]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+40]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+36]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 286331153
	and esi, 286331153
	mov edi, ebx
	mov ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+36]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+32]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+44]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+40]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 572662306
	and esi, 572662306
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+40]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+36]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+32]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+44]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 1145324612
	and esi, 1145324612
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+44]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+40]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+36]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+32]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, -2004318072
	and esi, -2004318072
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+176]
	mov edx, DWORD PTR [ecx+180]
	mov ebx, DWORD PTR [ecx+184]
	mov esi, DWORD PTR [ecx+188]
	xor edi, eax
	xor edi, ebx
	xor ebp, edx
	xor ebp, esi
	xor edx, edi
	xor ebx, ebp
	mov DWORD PTR [ecx+180], edx
	mov DWORD PTR [ecx+184], ebx
	mov eax, DWORD PTR [ecx+168]
	mov edx, eax
	and edx, 286331153
	mov DWORD PTR [ecx+144], edx
	mov edx, eax
	and edx, 572662306
	mov DWORD PTR [ecx+148], edx
	mov edx, eax
	and edx, 1145324612
	mov DWORD PTR [ecx+152], edx
	mov edx, eax
	and edx, -2004318072
	mov DWORD PTR [ecx+156], edx
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+48]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+60]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+56]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+52]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 286331153
	and esi, 286331153
	mov edi, ebx
	mov ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+52]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+48]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+60]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+56]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 572662306
	and esi, 572662306
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+56]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+52]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+48]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+60]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 1145324612
	and esi, 1145324612
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+60]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+56]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+52]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+48]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, -2004318072
	and esi, -2004318072
	xor edi, ebx
	xor ebp, esi
	mov DWORD PTR [ecx+192], edi
	mov DWORD PTR [ecx+196], ebp
	mov eax, DWORD PTR [ecx+172]
	mov edx, eax
	and edx, 286331153
	mov DWORD PTR [ecx+144], edx
	mov edx, eax
	and edx, 572662306
	mov DWORD PTR [ecx+148], edx
	mov edx, eax
	and edx, 1145324612
	mov DWORD PTR [ecx+152], edx
	mov edx, eax
	and edx, -2004318072
	mov DWORD PTR [ecx+156], edx
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+76]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+72]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 286331153
	and esi, 286331153
	mov edi, ebx
	mov ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+76]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+72]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 572662306
	and esi, 572662306
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+72]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+76]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 1145324612
	and esi, 1145324612
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+76]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+72]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+68]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+64]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, -2004318072
	and esi, -2004318072
	xor edi, ebx
	xor ebp, esi
	mov DWORD PTR [ecx+200], edi
	mov DWORD PTR [ecx+204], ebp
	mov eax, DWORD PTR [ecx+168]
	xor eax, DWORD PTR [ecx+172]
	mov edx, eax
	and edx, 286331153
	mov DWORD PTR [ecx+144], edx
	mov edx, eax
	and edx, 572662306
	mov DWORD PTR [ecx+148], edx
	mov edx, eax
	and edx, 1145324612
	mov DWORD PTR [ecx+152], edx
	mov edx, eax
	and edx, -2004318072
	mov DWORD PTR [ecx+156], edx
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+80]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+92]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+88]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+84]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 286331153
	and esi, 286331153
	mov edi, ebx
	mov ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+84]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+80]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+92]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+88]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 572662306
	and esi, 572662306
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+88]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+84]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+80]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+92]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 1145324612
	and esi, 1145324612
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+92]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+88]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+84]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+80]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, -2004318072
	and esi, -2004318072
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+192]
	mov edx, DWORD PTR [ecx+196]
	mov ebx, DWORD PTR [ecx+200]
	mov esi, DWORD PTR [ecx+204]
	xor edi, eax
	xor edi, ebx
	xor ebp, edx
	xor ebp, esi
	xor edx, edi
	xor ebx, ebp
	mov DWORD PTR [ecx+196], edx
	mov DWORD PTR [ecx+200], ebx
	mov eax, DWORD PTR [ecx+160]
	xor eax, DWORD PTR [ecx+168]
	mov edx, eax
	and edx, 286331153
	mov DWORD PTR [ecx+144], edx
	mov edx, eax
	and edx, 572662306
	mov DWORD PTR [ecx+148], edx
	mov edx, eax
	and edx, 1145324612
	mov DWORD PTR [ecx+152], edx
	mov edx, eax
	and edx, -2004318072
	mov DWORD PTR [ecx+156], edx
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+96]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+108]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+104]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+100]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 286331153
	and esi, 286331153
	mov edi, ebx
	mov ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+100]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+96]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+108]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+104]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 572662306
	and esi, 572662306
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+104]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+100]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+96]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+108]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 1145324612
	and esi, 1145324612
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+108]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+104]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+100]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+96]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, -2004318072
	and esi, -2004318072
	xor edi, ebx
	xor ebp, esi
	mov DWORD PTR [ecx+208], edi
	mov DWORD PTR [ecx+212], ebp
	mov eax, DWORD PTR [ecx+164]
	xor eax, DWORD PTR [ecx+172]
	mov edx, eax
	and edx, 286331153
	mov DWORD PTR [ecx+144], edx
	mov edx, eax
	and edx, 572662306
	mov DWORD PTR [ecx+148], edx
	mov edx, eax
	and edx, 1145324612
	mov DWORD PTR [ecx+152], edx
	mov edx, eax
	and edx, -2004318072
	mov DWORD PTR [ecx+156], edx
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+112]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+124]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+120]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+116]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 286331153
	and esi, 286331153
	mov edi, ebx
	mov ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+116]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+112]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+124]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+120]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 572662306
	and esi, 572662306
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+120]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+116]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+112]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+124]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 1145324612
	and esi, 1145324612
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+124]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+120]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+116]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+112]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, -2004318072
	and esi, -2004318072
	xor edi, ebx
	xor ebp, esi
	mov DWORD PTR [ecx+216], edi
	mov DWORD PTR [ecx+220], ebp
	mov eax, DWORD PTR [ecx+160]
	xor eax, DWORD PTR [ecx+168]
	xor eax, DWORD PTR [ecx+164]
	xor eax, DWORD PTR [ecx+172]
	mov edx, eax
	and edx, 286331153
	mov DWORD PTR [ecx+144], edx
	mov edx, eax
	and edx, 572662306
	mov DWORD PTR [ecx+148], edx
	mov edx, eax
	and edx, 1145324612
	mov DWORD PTR [ecx+152], edx
	mov edx, eax
	and edx, -2004318072
	mov DWORD PTR [ecx+156], edx
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+128]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+140]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+136]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+132]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 286331153
	and esi, 286331153
	mov edi, ebx
	mov ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+132]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+128]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+140]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+136]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 572662306
	and esi, 572662306
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+136]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+132]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+128]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+140]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 1145324612
	and esi, 1145324612
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+144]
	mov edx, DWORD PTR [ecx+140]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, DWORD PTR [ecx+136]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, DWORD PTR [ecx+132]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, DWORD PTR [ecx+128]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, -2004318072
	and esi, -2004318072
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+208]
	mov edx, DWORD PTR [ecx+212]
	mov ebx, DWORD PTR [ecx+216]
	mov esi, DWORD PTR [ecx+220]
	xor edi, eax
	xor edi, ebx
	xor ebp, edx
	xor ebp, esi
	xor edx, edi
	xor ebx, ebp
	mov DWORD PTR [ecx+212], edx
	mov DWORD PTR [ecx+216], ebx
	mov eax, DWORD PTR [ecx+176]
	mov ebx, eax
	shr ebx, 1
	mov esi, ebx
	shr ebx, 1
	xor esi, ebx
	shr ebx, 5
	xor esi, ebx
	ror eax, 1
	mov ebx, eax
	ror eax, 1
	xor ebx, eax
	ror eax, 5
	xor ebx, eax
	xor ebx, esi
	mov edx, DWORD PTR [ecx+212]
	xor edx, DWORD PTR [ecx+180]
	xor edx, DWORD PTR [ecx+196]
	xor edx, DWORD PTR [ecx+188]
	xor edx, ebx
	mov edi, DWORD PTR [ecx+192]
	xor edi, DWORD PTR [ecx+216]
	xor edi, DWORD PTR [ecx+184]
	xor edi, DWORD PTR [ecx+200]
	xor edi, DWORD PTR [ecx+176]
	xor edi, esi
	mov eax, DWORD PTR [ecx+180]
	mov ebx, eax
	shr ebx, 1
	mov esi, ebx
	shr ebx, 1
	xor esi, ebx
	shr ebx, 5
	xor esi, ebx
	ror eax, 1
	mov ebx, eax
	ror eax, 1
	xor ebx, eax
	ror eax, 5
	xor ebx, eax
	xor ebx, esi
	xor edi, ebx
	mov DWORD PTR [ecx+160], edi
	mov edi, DWORD PTR [ecx+196]
	xor edi, DWORD PTR [ecx+220]
	xor edi, DWORD PTR [ecx+188]
	xor edi, DWORD PTR [ecx+204]
	xor edi, DWORD PTR [ecx+180]
	xor edi, esi
	mov eax, DWORD PTR [ecx+208]
	xor eax, DWORD PTR [ecx+176]
	xor eax, DWORD PTR [ecx+192]
	xor eax, DWORD PTR [ecx+184]
	mov ebp, eax
	mov ebx, eax
	shr ebx, 1
	mov esi, ebx
	shr ebx, 1
	xor esi, ebx
	shr ebx, 5
	xor esi, ebx
	ror eax, 1
	mov ebx, eax
	ror eax, 1
	xor ebx, eax
	ror eax, 5
	xor ebx, eax
	xor ebx, esi
	xor edi, ebx
	mov DWORD PTR [ecx+164], edi
	mov edi, DWORD PTR [ecx+200]
	xor edi, ebp
	xor edi, esi
	mov eax, edx
	mov ebx, eax
	shr ebx, 1
	mov esi, ebx
	shr ebx, 1
	xor esi, ebx
	shr ebx, 5
	xor esi, ebx
	ror eax, 1
	mov ebx, eax
	ror eax, 1
	xor ebx, eax
	ror eax, 5
	xor ebx, eax
	xor ebx, esi
	xor edi, ebx
	mov DWORD PTR [ecx+168], edi
	mov edi, DWORD PTR [ecx+204]
	xor edi, edx
	xor edi, esi
	mov DWORD PTR [ecx+172], edi
	mov eax, DWORD PTR [ecx+244]
	add eax, -1
	mov DWORD PTR [ecx+244], eax
	test eax, eax
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ecx+172]
	mov ebx, DWORD PTR [ecx+168]
	mov esi, DWORD PTR [ecx+164]
	mov edi, DWORD PTR [ecx+160]
	bswap eax
	bswap ebx
	bswap esi
	bswap edi
	mov DWORD PTR [ecx+160], eax
	mov DWORD PTR [ecx+164], ebx
	mov DWORD PTR [ecx+168], esi
	mov DWORD PTR [ecx+172], edi
	mov ebx, DWORD PTR [ecx+224]
	mov esi, DWORD PTR [ecx+228]
	mov edi, DWORD PTR [ecx+232]
	mov ebp, DWORD PTR [ecx+236]
	mov edx, DWORD PTR [esp+8]
	movdqu xmm0, XMMWORD PTR [ecx+160]
	movdqu XMMWORD PTR [edx], xmm0
	ret
	.p2align 6
