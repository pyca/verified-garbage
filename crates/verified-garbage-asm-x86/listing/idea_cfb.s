// The functions of `src/idea_cfb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_idea_cfb64_encrypt:
	lea esp, [esp-208]
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+140], ebx
	mov DWORD PTR [eax+144], esi
	mov DWORD PTR [eax+148], edi
	mov DWORD PTR [eax+152], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+168], eax
	mov esi, edi
	mov edx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edx+12]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edx+16]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edx+20]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edx+24]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edx+28]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edx+32]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edx+36]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edx+40]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edx+44]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edx+48]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edx+52]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edx+56]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edx+60]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [edx+64]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edx+68]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edx+72]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edx+76]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edx+80]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edx+84]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edx+88]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edx+92]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edx+96]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [edx+100]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+160], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+156]
	mov ebp, DWORD PTR [edi+160]
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+136], eax
	mov esi, edi
	mov eax, edi
	add eax, 132
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [esi+108]
	mov ebx, DWORD PTR [eax]
	bswap ebx
	mov ecx, ebx
	shr ebx, 16
	and ecx, 65535
	mov edi, DWORD PTR [eax+4]
	bswap edi
	mov ebp, edi
	shr edi, 16
	and ebp, 65535
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+6]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add ecx, DWORD PTR [esi+2]
	and ecx, 65535
	add edi, DWORD PTR [esi+4]
	and edi, 65535
	mov eax, ebx
	xor eax, edi
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+8]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov DWORD PTR [esi+104], edx
	mov eax, ecx
	xor eax, ebp
	add eax, edx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+10]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov eax, DWORD PTR [esi+104]
	add eax, edx
	and eax, 65535
	xor ebx, edx
	xor edi, edx
	xor ecx, eax
	xor ebp, eax
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+12]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+18]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add edi, DWORD PTR [esi+14]
	and edi, 65535
	add ecx, DWORD PTR [esi+16]
	and ecx, 65535
	mov eax, ebx
	xor eax, ecx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+20]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov DWORD PTR [esi+104], edx
	mov eax, edi
	xor eax, ebp
	add eax, edx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+22]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov eax, DWORD PTR [esi+104]
	add eax, edx
	and eax, 65535
	xor ebx, edx
	xor ecx, edx
	xor edi, eax
	xor ebp, eax
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+24]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+30]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add ecx, DWORD PTR [esi+26]
	and ecx, 65535
	add edi, DWORD PTR [esi+28]
	and edi, 65535
	mov eax, ebx
	xor eax, edi
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+32]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov DWORD PTR [esi+104], edx
	mov eax, ecx
	xor eax, ebp
	add eax, edx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+34]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov eax, DWORD PTR [esi+104]
	add eax, edx
	and eax, 65535
	xor ebx, edx
	xor edi, edx
	xor ecx, eax
	xor ebp, eax
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+36]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+42]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add edi, DWORD PTR [esi+38]
	and edi, 65535
	add ecx, DWORD PTR [esi+40]
	and ecx, 65535
	mov eax, ebx
	xor eax, ecx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+44]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov DWORD PTR [esi+104], edx
	mov eax, edi
	xor eax, ebp
	add eax, edx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+46]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov eax, DWORD PTR [esi+104]
	add eax, edx
	and eax, 65535
	xor ebx, edx
	xor ecx, edx
	xor edi, eax
	xor ebp, eax
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+48]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+54]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add ecx, DWORD PTR [esi+50]
	and ecx, 65535
	add edi, DWORD PTR [esi+52]
	and edi, 65535
	mov eax, ebx
	xor eax, edi
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+56]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov DWORD PTR [esi+104], edx
	mov eax, ecx
	xor eax, ebp
	add eax, edx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+58]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov eax, DWORD PTR [esi+104]
	add eax, edx
	and eax, 65535
	xor ebx, edx
	xor edi, edx
	xor ecx, eax
	xor ebp, eax
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+60]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+66]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add edi, DWORD PTR [esi+62]
	and edi, 65535
	add ecx, DWORD PTR [esi+64]
	and ecx, 65535
	mov eax, ebx
	xor eax, ecx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+68]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov DWORD PTR [esi+104], edx
	mov eax, edi
	xor eax, ebp
	add eax, edx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+70]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov eax, DWORD PTR [esi+104]
	add eax, edx
	and eax, 65535
	xor ebx, edx
	xor ecx, edx
	xor edi, eax
	xor ebp, eax
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+72]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+78]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add ecx, DWORD PTR [esi+74]
	and ecx, 65535
	add edi, DWORD PTR [esi+76]
	and edi, 65535
	mov eax, ebx
	xor eax, edi
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+80]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov DWORD PTR [esi+104], edx
	mov eax, ecx
	xor eax, ebp
	add eax, edx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+82]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov eax, DWORD PTR [esi+104]
	add eax, edx
	and eax, 65535
	xor ebx, edx
	xor edi, edx
	xor ecx, eax
	xor ebp, eax
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+84]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+90]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add edi, DWORD PTR [esi+86]
	and edi, 65535
	add ecx, DWORD PTR [esi+88]
	and ecx, 65535
	mov eax, ebx
	xor eax, ecx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+92]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov DWORD PTR [esi+104], edx
	mov eax, edi
	xor eax, ebp
	add eax, edx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+94]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov eax, DWORD PTR [esi+104]
	add eax, edx
	and eax, 65535
	xor ebx, edx
	xor ecx, edx
	xor edi, eax
	xor ebp, eax
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+96]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+102]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add edi, DWORD PTR [esi+98]
	and edi, 65535
	add ecx, DWORD PTR [esi+100]
	and ecx, 65535
	ror ebx, 16
	or ebx, edi
	bswap ebx
	mov DWORD PTR [esi+132], ebx
	ror ecx, 16
	or ecx, ebp
	bswap ecx
	mov DWORD PTR [esi+136], ecx
	mov edi, esi
	mov esi, DWORD PTR [edi+156]
	mov ebp, DWORD PTR [edi+160]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+132]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+136]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+168], eax
	add esi, 8
	sub ebp, 1
	mov DWORD PTR [edi+156], esi
	mov DWORD PTR [edi+160], ebp
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+140]
	mov esi, DWORD PTR [edi+144]
	mov ebp, DWORD PTR [edi+152]
	mov edi, DWORD PTR [edi+148]
	mov ecx, 0
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	lea esp, [esp+208]
	ret
	.p2align 6

vg_idea_cfb64_decrypt:
	lea esp, [esp-208]
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+140], ebx
	mov DWORD PTR [eax+144], esi
	mov DWORD PTR [eax+148], edi
	mov DWORD PTR [eax+152], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+168], eax
	mov esi, edi
	mov edx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edx+12]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edx+16]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edx+20]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edx+24]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edx+28]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edx+32]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edx+36]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edx+40]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edx+44]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edx+48]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edx+52]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edx+56]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edx+60]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [edx+64]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edx+68]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edx+72]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edx+76]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edx+80]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edx+84]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edx+88]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edx+92]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edx+96]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [edx+100]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+160], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+156]
	mov ebp, DWORD PTR [edi+160]
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+136], eax
	mov esi, edi
	mov eax, edi
	add eax, 132
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [esi+108]
	mov ebx, DWORD PTR [eax]
	bswap ebx
	mov ecx, ebx
	shr ebx, 16
	and ecx, 65535
	mov edi, DWORD PTR [eax+4]
	bswap edi
	mov ebp, edi
	shr edi, 16
	and ebp, 65535
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+6]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add ecx, DWORD PTR [esi+2]
	and ecx, 65535
	add edi, DWORD PTR [esi+4]
	and edi, 65535
	mov eax, ebx
	xor eax, edi
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+8]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov DWORD PTR [esi+104], edx
	mov eax, ecx
	xor eax, ebp
	add eax, edx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+10]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov eax, DWORD PTR [esi+104]
	add eax, edx
	and eax, 65535
	xor ebx, edx
	xor edi, edx
	xor ecx, eax
	xor ebp, eax
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+12]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+18]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add edi, DWORD PTR [esi+14]
	and edi, 65535
	add ecx, DWORD PTR [esi+16]
	and ecx, 65535
	mov eax, ebx
	xor eax, ecx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+20]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov DWORD PTR [esi+104], edx
	mov eax, edi
	xor eax, ebp
	add eax, edx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+22]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov eax, DWORD PTR [esi+104]
	add eax, edx
	and eax, 65535
	xor ebx, edx
	xor ecx, edx
	xor edi, eax
	xor ebp, eax
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+24]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+30]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add ecx, DWORD PTR [esi+26]
	and ecx, 65535
	add edi, DWORD PTR [esi+28]
	and edi, 65535
	mov eax, ebx
	xor eax, edi
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+32]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov DWORD PTR [esi+104], edx
	mov eax, ecx
	xor eax, ebp
	add eax, edx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+34]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov eax, DWORD PTR [esi+104]
	add eax, edx
	and eax, 65535
	xor ebx, edx
	xor edi, edx
	xor ecx, eax
	xor ebp, eax
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+36]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+42]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add edi, DWORD PTR [esi+38]
	and edi, 65535
	add ecx, DWORD PTR [esi+40]
	and ecx, 65535
	mov eax, ebx
	xor eax, ecx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+44]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov DWORD PTR [esi+104], edx
	mov eax, edi
	xor eax, ebp
	add eax, edx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+46]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov eax, DWORD PTR [esi+104]
	add eax, edx
	and eax, 65535
	xor ebx, edx
	xor ecx, edx
	xor edi, eax
	xor ebp, eax
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+48]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+54]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add ecx, DWORD PTR [esi+50]
	and ecx, 65535
	add edi, DWORD PTR [esi+52]
	and edi, 65535
	mov eax, ebx
	xor eax, edi
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+56]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov DWORD PTR [esi+104], edx
	mov eax, ecx
	xor eax, ebp
	add eax, edx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+58]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov eax, DWORD PTR [esi+104]
	add eax, edx
	and eax, 65535
	xor ebx, edx
	xor edi, edx
	xor ecx, eax
	xor ebp, eax
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+60]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+66]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add edi, DWORD PTR [esi+62]
	and edi, 65535
	add ecx, DWORD PTR [esi+64]
	and ecx, 65535
	mov eax, ebx
	xor eax, ecx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+68]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov DWORD PTR [esi+104], edx
	mov eax, edi
	xor eax, ebp
	add eax, edx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+70]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov eax, DWORD PTR [esi+104]
	add eax, edx
	and eax, 65535
	xor ebx, edx
	xor ecx, edx
	xor edi, eax
	xor ebp, eax
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+72]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+78]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add ecx, DWORD PTR [esi+74]
	and ecx, 65535
	add edi, DWORD PTR [esi+76]
	and edi, 65535
	mov eax, ebx
	xor eax, edi
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+80]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov DWORD PTR [esi+104], edx
	mov eax, ecx
	xor eax, ebp
	add eax, edx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+82]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov eax, DWORD PTR [esi+104]
	add eax, edx
	and eax, 65535
	xor ebx, edx
	xor edi, edx
	xor ecx, eax
	xor ebp, eax
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+84]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+90]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add edi, DWORD PTR [esi+86]
	and edi, 65535
	add ecx, DWORD PTR [esi+88]
	and ecx, 65535
	mov eax, ebx
	xor eax, ecx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+92]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov DWORD PTR [esi+104], edx
	mov eax, edi
	xor eax, ebp
	add eax, edx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+94]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov eax, DWORD PTR [esi+104]
	add eax, edx
	and eax, 65535
	xor ebx, edx
	xor ecx, edx
	xor edi, eax
	xor ebp, eax
	mov eax, ebx
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+96]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebx, edx
	mov eax, ebp
	sub eax, 1
	and eax, 65535
	add eax, 1
	mov edx, DWORD PTR [esi+102]
	sub edx, 1
	and edx, 65535
	add edx, 1
	mul edx
	sub eax, 1
	mov edx, eax
	and edx, 65535
	add edx, 1
	shr eax, 16
	sub edx, eax
	mov eax, edx
	shr eax, 31
	add edx, eax
	and edx, 65535
	mov ebp, edx
	add edi, DWORD PTR [esi+98]
	and edi, 65535
	add ecx, DWORD PTR [esi+100]
	and ecx, 65535
	ror ebx, 16
	or ebx, edi
	bswap ebx
	mov DWORD PTR [esi+132], ebx
	ror ecx, 16
	or ecx, ebp
	bswap ecx
	mov DWORD PTR [esi+136], ecx
	mov edi, esi
	mov esi, DWORD PTR [edi+156]
	mov ebp, DWORD PTR [edi+160]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+132]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+136]
	mov DWORD PTR [esi+4], eax
	add esi, 8
	sub ebp, 1
	mov DWORD PTR [edi+156], esi
	mov DWORD PTR [edi+160], ebp
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+140]
	mov esi, DWORD PTR [edi+144]
	mov ebp, DWORD PTR [edi+152]
	mov edi, DWORD PTR [edi+148]
	mov ecx, 0
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	lea esp, [esp+208]
	ret
	.p2align 6
