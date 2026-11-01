// The functions of `src/ed448.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_public_key:
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	mov eax, DWORD PTR [esp+268]
	mov edx, 0
	mov DWORD PTR [eax], edx
	mov DWORD PTR [eax+4], edx
	mov DWORD PTR [eax+8], edx
	mov DWORD PTR [eax+12], edx
	mov DWORD PTR [eax+16], edx
	mov DWORD PTR [eax+20], edx
	mov DWORD PTR [eax+24], edx
	mov DWORD PTR [eax+28], edx
	mov DWORD PTR [eax+32], edx
	mov DWORD PTR [eax+36], edx
	mov DWORD PTR [eax+40], edx
	mov DWORD PTR [eax+44], edx
	mov DWORD PTR [eax+48], edx
	mov DWORD PTR [eax+52], edx
	mov DWORD PTR [eax+56], edx
	mov DWORD PTR [eax+60], edx
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
	mov DWORD PTR [eax+192], edx
	mov DWORD PTR [eax+196], edx
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+264]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 57
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, 31
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 208
	mov DWORD PTR [esp+16], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_pad_scratch}
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+12], eax
	mov eax, 114
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_squeeze_scratch}
	movzx eax, BYTE PTR [esp+24]
	and eax, 252
	mov BYTE PTR [esp+24], al
	movzx eax, BYTE PTR [esp+79]
	or eax, 128
	mov BYTE PTR [esp+79], al
	mov eax, 0
	mov BYTE PTR [esp+80], al
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed448_scalar_base}
	mov eax, 0
	mov DWORD PTR [esp+24], eax
	mov eax, 0
	mov DWORD PTR [esp+28], eax
	mov eax, 0
	mov DWORD PTR [esp+32], eax
	mov eax, 0
	mov DWORD PTR [esp+36], eax
	mov eax, 0
	mov DWORD PTR [esp+40], eax
	mov eax, 0
	mov DWORD PTR [esp+44], eax
	mov eax, 0
	mov DWORD PTR [esp+48], eax
	mov eax, 0
	mov DWORD PTR [esp+52], eax
	mov eax, 0
	mov DWORD PTR [esp+56], eax
	mov eax, 0
	mov DWORD PTR [esp+60], eax
	mov eax, 0
	mov DWORD PTR [esp+64], eax
	mov eax, 0
	mov DWORD PTR [esp+68], eax
	mov eax, 0
	mov DWORD PTR [esp+72], eax
	mov eax, 0
	mov DWORD PTR [esp+76], eax
	mov eax, 0
	mov DWORD PTR [esp+80], eax
	mov eax, 0
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+88], eax
	mov eax, 0
	mov DWORD PTR [esp+92], eax
	mov eax, 0
	mov DWORD PTR [esp+96], eax
	mov eax, 0
	mov DWORD PTR [esp+100], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov eax, 0
	mov DWORD PTR [esp+108], eax
	mov eax, 0
	mov DWORD PTR [esp+112], eax
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov eax, 0
	mov DWORD PTR [esp+120], eax
	mov eax, 0
	mov DWORD PTR [esp+124], eax
	mov eax, 0
	mov DWORD PTR [esp+128], eax
	mov eax, 0
	mov DWORD PTR [esp+132], eax
	mov eax, 0
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+140], eax
	mov eax, 0
	mov DWORD PTR [esp+144], eax
	mov eax, 0
	mov DWORD PTR [esp+148], eax
	mov eax, 0
	mov DWORD PTR [esp+152], eax
	mov eax, 0
	mov DWORD PTR [esp+156], eax
	mov eax, 0
	mov DWORD PTR [esp+160], eax
	mov eax, 0
	mov DWORD PTR [esp+164], eax
	mov eax, 0
	mov DWORD PTR [esp+168], eax
	mov eax, 0
	mov DWORD PTR [esp+172], eax
	mov eax, 0
	mov DWORD PTR [esp+176], eax
	mov eax, 0
	mov DWORD PTR [esp+180], eax
	mov eax, 0
	mov DWORD PTR [esp+184], eax
	mov eax, 0
	mov DWORD PTR [esp+188], eax
	mov eax, 0
	mov DWORD PTR [esp+192], eax
	mov eax, 0
	mov DWORD PTR [esp+196], eax
	mov eax, 0
	mov DWORD PTR [esp+200], eax
	mov eax, 0
	mov DWORD PTR [esp+204], eax
	mov eax, 0
	mov DWORD PTR [esp+208], eax
	mov eax, 0
	mov DWORD PTR [esp+212], eax
	mov eax, 0
	mov DWORD PTR [esp+216], eax
	mov eax, 0
	mov DWORD PTR [esp+220], eax
	mov eax, 0
	mov DWORD PTR [esp+224], eax
	mov eax, 0
	mov DWORD PTR [esp+228], eax
	mov eax, 0
	mov DWORD PTR [esp+232], eax
	mov eax, 0
	mov DWORD PTR [esp+236], eax
	mov eax, 0
	mov DWORD PTR [esp+240], eax
	mov eax, 0
	mov DWORD PTR [esp+244], eax
	mov eax, 0
	mov DWORD PTR [esp+248], eax
	mov eax, 0
	mov DWORD PTR [esp+252], eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	ret
	.p2align 6

vg_ed448_scalar_reduce:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, 0
	mov DWORD PTR [edi+192], eax
	mov DWORD PTR [edi+196], eax
	mov DWORD PTR [edi+200], eax
	mov DWORD PTR [edi+204], eax
	mov DWORD PTR [edi+208], eax
	mov DWORD PTR [edi+212], eax
	mov DWORD PTR [edi+216], eax
	mov DWORD PTR [edi+220], eax
	mov DWORD PTR [edi+224], eax
	mov DWORD PTR [edi+228], eax
	mov DWORD PTR [edi+232], eax
	mov DWORD PTR [edi+236], eax
	mov DWORD PTR [edi+240], eax
	mov DWORD PTR [edi+244], eax
	mov DWORD PTR [edi+248], eax
	mov DWORD PTR [edi+252], eax
	mov DWORD PTR [edi+256], eax
	mov DWORD PTR [edi+260], eax
	mov DWORD PTR [edi+264], eax
	mov DWORD PTR [edi+268], eax
	mov DWORD PTR [edi+272], eax
	mov DWORD PTR [edi+276], eax
	mov DWORD PTR [edi+280], eax
	mov DWORD PTR [edi+284], eax
	mov DWORD PTR [edi+288], eax
	mov DWORD PTR [edi+292], eax
	mov DWORD PTR [edi+296], eax
	mov DWORD PTR [edi+300], eax
	mov ebp, 114
20:
	sub ebp, 2
	mov edx, esi
	add edx, ebp
	movzx eax, BYTE PTR [edx]
	movzx edx, BYTE PTR [edx+1]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+16], eax
	mov ecx, DWORD PTR [edi+296]
	shr ecx, 14
	mov eax, DWORD PTR [edi+300]
	ror eax, 30
	add ecx, eax
	mov ebx, 0
	mov eax, 47885
	mul ecx
	add eax, DWORD PTR [edi+16]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+64], edx
	shr ebx, 16
	mov eax, 21671
	mul ecx
	add eax, DWORD PTR [edi+192]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+68], edx
	shr ebx, 16
	mov eax, 15725
	mul ecx
	add eax, DWORD PTR [edi+196]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+72], edx
	shr ebx, 16
	mov eax, 56455
	mul ecx
	add eax, DWORD PTR [edi+200]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+76], edx
	shr ebx, 16
	mov eax, 28842
	mul ecx
	add eax, DWORD PTR [edi+204]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+80], edx
	shr ebx, 16
	mov eax, 29242
	mul ecx
	add eax, DWORD PTR [edi+208]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+84], edx
	shr ebx, 16
	mov eax, 15757
	mul ecx
	add eax, DWORD PTR [edi+212]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+88], edx
	shr ebx, 16
	mov eax, 56979
	mul ecx
	add eax, DWORD PTR [edi+216]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+92], edx
	shr ebx, 16
	mov eax, 51567
	mul ecx
	add eax, DWORD PTR [edi+220]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+96], edx
	shr ebx, 16
	mov eax, 20777
	mul ecx
	add eax, DWORD PTR [edi+224]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+100], edx
	shr ebx, 16
	mov eax, 9398
	mul ecx
	add eax, DWORD PTR [edi+228]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+104], edx
	shr ebx, 16
	mov eax, 15281
	mul ecx
	add eax, DWORD PTR [edi+232]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+108], edx
	shr ebx, 16
	mov eax, 56342
	mul ecx
	add eax, DWORD PTR [edi+236]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+112], edx
	shr ebx, 16
	mov eax, 33589
	mul ecx
	add eax, DWORD PTR [edi+240]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+116], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+244]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+120], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+248]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+124], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+252]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+128], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+256]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+132], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+260]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+136], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+264]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+140], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+268]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+144], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+272]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+148], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+276]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+152], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+280]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+156], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+284]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+160], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+288]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+164], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+292]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+168], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+296]
	and eax, 16383
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+172], edx
	shr ebx, 16
	mov ebx, 0
	mov eax, DWORD PTR [edi+64]
	add eax, 47885
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+192], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+68]
	add eax, 21671
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+196], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+72]
	add eax, 15725
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+200], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+76]
	add eax, 56455
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+204], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+80]
	add eax, 28842
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+208], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+84]
	add eax, 29242
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+212], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+88]
	add eax, 15757
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+216], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+92]
	add eax, 56979
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+220], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+96]
	add eax, 51567
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+224], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+100]
	add eax, 20777
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+228], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+104]
	add eax, 9398
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+232], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+108]
	add eax, 15281
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+236], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+112]
	add eax, 56342
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+240], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+116]
	add eax, 33589
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+244], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+120]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+248], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+124]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+252], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+128]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+256], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+132]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+260], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+136]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+264], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+140]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+268], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+144]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+272], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+148]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+276], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+152]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+280], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+156]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+284], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+160]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+288], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+164]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+292], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+168]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+296], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+172]
	add eax, 49152
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+300], edx
	shr ebx, 16
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+192]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+196]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+200]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+204]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+208]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+212]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+216]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+220]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+224]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+228]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+232]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+236]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+240]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+244]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+248]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+252]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+256]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+260]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+156]
	mov edx, DWORD PTR [edi+284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+300], eax
	cmp ebp, 0
	jne 20b
	mov esi, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+192]
	mov BYTE PTR [esi], al
	shr eax, 8
	mov BYTE PTR [esi+1], al
	mov eax, DWORD PTR [edi+196]
	mov BYTE PTR [esi+2], al
	shr eax, 8
	mov BYTE PTR [esi+3], al
	mov eax, DWORD PTR [edi+200]
	mov BYTE PTR [esi+4], al
	shr eax, 8
	mov BYTE PTR [esi+5], al
	mov eax, DWORD PTR [edi+204]
	mov BYTE PTR [esi+6], al
	shr eax, 8
	mov BYTE PTR [esi+7], al
	mov eax, DWORD PTR [edi+208]
	mov BYTE PTR [esi+8], al
	shr eax, 8
	mov BYTE PTR [esi+9], al
	mov eax, DWORD PTR [edi+212]
	mov BYTE PTR [esi+10], al
	shr eax, 8
	mov BYTE PTR [esi+11], al
	mov eax, DWORD PTR [edi+216]
	mov BYTE PTR [esi+12], al
	shr eax, 8
	mov BYTE PTR [esi+13], al
	mov eax, DWORD PTR [edi+220]
	mov BYTE PTR [esi+14], al
	shr eax, 8
	mov BYTE PTR [esi+15], al
	mov eax, DWORD PTR [edi+224]
	mov BYTE PTR [esi+16], al
	shr eax, 8
	mov BYTE PTR [esi+17], al
	mov eax, DWORD PTR [edi+228]
	mov BYTE PTR [esi+18], al
	shr eax, 8
	mov BYTE PTR [esi+19], al
	mov eax, DWORD PTR [edi+232]
	mov BYTE PTR [esi+20], al
	shr eax, 8
	mov BYTE PTR [esi+21], al
	mov eax, DWORD PTR [edi+236]
	mov BYTE PTR [esi+22], al
	shr eax, 8
	mov BYTE PTR [esi+23], al
	mov eax, DWORD PTR [edi+240]
	mov BYTE PTR [esi+24], al
	shr eax, 8
	mov BYTE PTR [esi+25], al
	mov eax, DWORD PTR [edi+244]
	mov BYTE PTR [esi+26], al
	shr eax, 8
	mov BYTE PTR [esi+27], al
	mov eax, DWORD PTR [edi+248]
	mov BYTE PTR [esi+28], al
	shr eax, 8
	mov BYTE PTR [esi+29], al
	mov eax, DWORD PTR [edi+252]
	mov BYTE PTR [esi+30], al
	shr eax, 8
	mov BYTE PTR [esi+31], al
	mov eax, DWORD PTR [edi+256]
	mov BYTE PTR [esi+32], al
	shr eax, 8
	mov BYTE PTR [esi+33], al
	mov eax, DWORD PTR [edi+260]
	mov BYTE PTR [esi+34], al
	shr eax, 8
	mov BYTE PTR [esi+35], al
	mov eax, DWORD PTR [edi+264]
	mov BYTE PTR [esi+36], al
	shr eax, 8
	mov BYTE PTR [esi+37], al
	mov eax, DWORD PTR [edi+268]
	mov BYTE PTR [esi+38], al
	shr eax, 8
	mov BYTE PTR [esi+39], al
	mov eax, DWORD PTR [edi+272]
	mov BYTE PTR [esi+40], al
	shr eax, 8
	mov BYTE PTR [esi+41], al
	mov eax, DWORD PTR [edi+276]
	mov BYTE PTR [esi+42], al
	shr eax, 8
	mov BYTE PTR [esi+43], al
	mov eax, DWORD PTR [edi+280]
	mov BYTE PTR [esi+44], al
	shr eax, 8
	mov BYTE PTR [esi+45], al
	mov eax, DWORD PTR [edi+284]
	mov BYTE PTR [esi+46], al
	shr eax, 8
	mov BYTE PTR [esi+47], al
	mov eax, DWORD PTR [edi+288]
	mov BYTE PTR [esi+48], al
	shr eax, 8
	mov BYTE PTR [esi+49], al
	mov eax, DWORD PTR [edi+292]
	mov BYTE PTR [esi+50], al
	shr eax, 8
	mov BYTE PTR [esi+51], al
	mov eax, DWORD PTR [edi+296]
	mov BYTE PTR [esi+52], al
	shr eax, 8
	mov BYTE PTR [esi+53], al
	mov eax, DWORD PTR [edi+300]
	mov BYTE PTR [esi+54], al
	shr eax, 8
	mov BYTE PTR [esi+55], al
	mov eax, 0
	mov BYTE PTR [esi+56], al
	mov eax, edi
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov ebp, DWORD PTR [eax+12]
	mov edi, DWORD PTR [eax+8]
	ret
	.p2align 6

vg_ed448_scalar_mul_add:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, 0
	mov DWORD PTR [edi+320], eax
	mov DWORD PTR [edi+324], eax
	mov DWORD PTR [edi+328], eax
	mov DWORD PTR [edi+332], eax
	mov DWORD PTR [edi+336], eax
	mov DWORD PTR [edi+340], eax
	mov DWORD PTR [edi+344], eax
	mov DWORD PTR [edi+348], eax
	mov DWORD PTR [edi+352], eax
	mov DWORD PTR [edi+356], eax
	mov DWORD PTR [edi+360], eax
	mov DWORD PTR [edi+364], eax
	mov DWORD PTR [edi+368], eax
	mov DWORD PTR [edi+372], eax
	mov DWORD PTR [edi+376], eax
	mov DWORD PTR [edi+380], eax
	mov DWORD PTR [edi+384], eax
	mov DWORD PTR [edi+388], eax
	mov DWORD PTR [edi+392], eax
	mov DWORD PTR [edi+396], eax
	mov DWORD PTR [edi+400], eax
	mov DWORD PTR [edi+404], eax
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+412], eax
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+420], eax
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+428], eax
	movzx eax, BYTE PTR [esi+56]
	mov DWORD PTR [edi+320], eax
	mov ebp, 56
20:
	sub ebp, 2
	mov edx, esi
	add edx, ebp
	movzx eax, BYTE PTR [edx]
	movzx edx, BYTE PTR [edx+1]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+16], eax
	mov ecx, DWORD PTR [edi+424]
	shr ecx, 14
	mov eax, DWORD PTR [edi+428]
	ror eax, 30
	add ecx, eax
	mov ebx, 0
	mov eax, 47885
	mul ecx
	add eax, DWORD PTR [edi+16]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+64], edx
	shr ebx, 16
	mov eax, 21671
	mul ecx
	add eax, DWORD PTR [edi+320]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+68], edx
	shr ebx, 16
	mov eax, 15725
	mul ecx
	add eax, DWORD PTR [edi+324]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+72], edx
	shr ebx, 16
	mov eax, 56455
	mul ecx
	add eax, DWORD PTR [edi+328]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+76], edx
	shr ebx, 16
	mov eax, 28842
	mul ecx
	add eax, DWORD PTR [edi+332]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+80], edx
	shr ebx, 16
	mov eax, 29242
	mul ecx
	add eax, DWORD PTR [edi+336]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+84], edx
	shr ebx, 16
	mov eax, 15757
	mul ecx
	add eax, DWORD PTR [edi+340]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+88], edx
	shr ebx, 16
	mov eax, 56979
	mul ecx
	add eax, DWORD PTR [edi+344]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+92], edx
	shr ebx, 16
	mov eax, 51567
	mul ecx
	add eax, DWORD PTR [edi+348]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+96], edx
	shr ebx, 16
	mov eax, 20777
	mul ecx
	add eax, DWORD PTR [edi+352]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+100], edx
	shr ebx, 16
	mov eax, 9398
	mul ecx
	add eax, DWORD PTR [edi+356]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+104], edx
	shr ebx, 16
	mov eax, 15281
	mul ecx
	add eax, DWORD PTR [edi+360]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+108], edx
	shr ebx, 16
	mov eax, 56342
	mul ecx
	add eax, DWORD PTR [edi+364]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+112], edx
	shr ebx, 16
	mov eax, 33589
	mul ecx
	add eax, DWORD PTR [edi+368]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+116], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+372]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+120], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+376]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+124], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+380]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+128], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+384]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+132], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+388]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+136], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+392]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+140], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+396]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+144], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+400]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+148], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+404]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+152], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+408]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+156], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+412]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+160], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+416]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+164], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+420]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+168], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+424]
	and eax, 16383
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+172], edx
	shr ebx, 16
	mov ebx, 0
	mov eax, DWORD PTR [edi+64]
	add eax, 47885
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+320], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+68]
	add eax, 21671
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+324], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+72]
	add eax, 15725
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+328], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+76]
	add eax, 56455
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+332], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+80]
	add eax, 28842
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+336], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+84]
	add eax, 29242
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+340], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+88]
	add eax, 15757
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+344], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+92]
	add eax, 56979
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+348], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+96]
	add eax, 51567
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+352], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+100]
	add eax, 20777
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+356], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+104]
	add eax, 9398
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+360], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+108]
	add eax, 15281
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+364], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+112]
	add eax, 56342
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+368], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+116]
	add eax, 33589
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+372], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+120]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+376], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+124]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+380], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+128]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+384], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+132]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+388], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+136]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+392], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+140]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+396], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+144]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+400], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+148]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+404], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+152]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+408], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+156]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+412], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+160]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+416], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+164]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+420], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+168]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+424], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+172]
	add eax, 49152
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+428], edx
	shr ebx, 16
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+320]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+324]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+328]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+332]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+336]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+340]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+344]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+348]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+352]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+356]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+360]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+364]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+368]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+372]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+376]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+380]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+384]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+388]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+392]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+396]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+400]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+404]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+408]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+156]
	mov edx, DWORD PTR [edi+412]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+416]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+420]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+424]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+428]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+428], eax
	cmp ebp, 0
	jne 20b
	mov esi, DWORD PTR [esp+16]
	mov eax, 0
	mov DWORD PTR [edi+448], eax
	mov DWORD PTR [edi+452], eax
	mov DWORD PTR [edi+456], eax
	mov DWORD PTR [edi+460], eax
	mov DWORD PTR [edi+464], eax
	mov DWORD PTR [edi+468], eax
	mov DWORD PTR [edi+472], eax
	mov DWORD PTR [edi+476], eax
	mov DWORD PTR [edi+480], eax
	mov DWORD PTR [edi+484], eax
	mov DWORD PTR [edi+488], eax
	mov DWORD PTR [edi+492], eax
	mov DWORD PTR [edi+496], eax
	mov DWORD PTR [edi+500], eax
	mov DWORD PTR [edi+504], eax
	mov DWORD PTR [edi+508], eax
	mov DWORD PTR [edi+512], eax
	mov DWORD PTR [edi+516], eax
	mov DWORD PTR [edi+520], eax
	mov DWORD PTR [edi+524], eax
	mov DWORD PTR [edi+528], eax
	mov DWORD PTR [edi+532], eax
	mov DWORD PTR [edi+536], eax
	mov DWORD PTR [edi+540], eax
	mov DWORD PTR [edi+544], eax
	mov DWORD PTR [edi+548], eax
	mov DWORD PTR [edi+552], eax
	mov DWORD PTR [edi+556], eax
	movzx eax, BYTE PTR [esi+56]
	mov DWORD PTR [edi+448], eax
	mov ebp, 56
21:
	sub ebp, 2
	mov edx, esi
	add edx, ebp
	movzx eax, BYTE PTR [edx]
	movzx edx, BYTE PTR [edx+1]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+16], eax
	mov ecx, DWORD PTR [edi+552]
	shr ecx, 14
	mov eax, DWORD PTR [edi+556]
	ror eax, 30
	add ecx, eax
	mov ebx, 0
	mov eax, 47885
	mul ecx
	add eax, DWORD PTR [edi+16]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+64], edx
	shr ebx, 16
	mov eax, 21671
	mul ecx
	add eax, DWORD PTR [edi+448]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+68], edx
	shr ebx, 16
	mov eax, 15725
	mul ecx
	add eax, DWORD PTR [edi+452]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+72], edx
	shr ebx, 16
	mov eax, 56455
	mul ecx
	add eax, DWORD PTR [edi+456]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+76], edx
	shr ebx, 16
	mov eax, 28842
	mul ecx
	add eax, DWORD PTR [edi+460]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+80], edx
	shr ebx, 16
	mov eax, 29242
	mul ecx
	add eax, DWORD PTR [edi+464]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+84], edx
	shr ebx, 16
	mov eax, 15757
	mul ecx
	add eax, DWORD PTR [edi+468]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+88], edx
	shr ebx, 16
	mov eax, 56979
	mul ecx
	add eax, DWORD PTR [edi+472]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+92], edx
	shr ebx, 16
	mov eax, 51567
	mul ecx
	add eax, DWORD PTR [edi+476]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+96], edx
	shr ebx, 16
	mov eax, 20777
	mul ecx
	add eax, DWORD PTR [edi+480]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+100], edx
	shr ebx, 16
	mov eax, 9398
	mul ecx
	add eax, DWORD PTR [edi+484]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+104], edx
	shr ebx, 16
	mov eax, 15281
	mul ecx
	add eax, DWORD PTR [edi+488]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+108], edx
	shr ebx, 16
	mov eax, 56342
	mul ecx
	add eax, DWORD PTR [edi+492]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+112], edx
	shr ebx, 16
	mov eax, 33589
	mul ecx
	add eax, DWORD PTR [edi+496]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+116], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+500]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+120], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+504]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+124], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+508]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+128], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+512]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+132], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+516]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+136], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+520]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+140], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+524]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+144], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+528]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+148], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+532]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+152], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+536]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+156], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+540]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+160], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+544]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+164], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+548]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+168], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+552]
	and eax, 16383
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+172], edx
	shr ebx, 16
	mov ebx, 0
	mov eax, DWORD PTR [edi+64]
	add eax, 47885
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+448], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+68]
	add eax, 21671
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+452], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+72]
	add eax, 15725
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+456], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+76]
	add eax, 56455
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+460], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+80]
	add eax, 28842
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+464], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+84]
	add eax, 29242
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+468], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+88]
	add eax, 15757
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+472], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+92]
	add eax, 56979
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+476], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+96]
	add eax, 51567
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+480], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+100]
	add eax, 20777
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+484], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+104]
	add eax, 9398
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+488], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+108]
	add eax, 15281
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+492], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+112]
	add eax, 56342
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+496], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+116]
	add eax, 33589
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+500], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+120]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+504], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+124]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+508], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+128]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+512], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+132]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+516], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+136]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+520], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+140]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+524], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+144]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+528], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+148]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+532], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+152]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+536], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+156]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+540], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+160]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+544], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+164]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+548], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+168]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+552], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+172]
	add eax, 49152
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+556], edx
	shr ebx, 16
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+448]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+452]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+456]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+460]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+464]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+468]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+472]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+476]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+480]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+484]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+488]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+492]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+496]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+500]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+504]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+508]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+508], eax
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+512]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+516]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+520]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+524]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+528]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+532]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+536]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+156]
	mov edx, DWORD PTR [edi+540]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+540], eax
	mov eax, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+544]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+548]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+552]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+556]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+556], eax
	cmp ebp, 0
	jne 21b
	mov esi, DWORD PTR [esp+8]
	mov eax, 0
	mov DWORD PTR [edi+576], eax
	mov DWORD PTR [edi+580], eax
	mov DWORD PTR [edi+584], eax
	mov DWORD PTR [edi+588], eax
	mov DWORD PTR [edi+592], eax
	mov DWORD PTR [edi+596], eax
	mov DWORD PTR [edi+600], eax
	mov DWORD PTR [edi+604], eax
	mov DWORD PTR [edi+608], eax
	mov DWORD PTR [edi+612], eax
	mov DWORD PTR [edi+616], eax
	mov DWORD PTR [edi+620], eax
	mov DWORD PTR [edi+624], eax
	mov DWORD PTR [edi+628], eax
	mov DWORD PTR [edi+632], eax
	mov DWORD PTR [edi+636], eax
	mov DWORD PTR [edi+640], eax
	mov DWORD PTR [edi+644], eax
	mov DWORD PTR [edi+648], eax
	mov DWORD PTR [edi+652], eax
	mov DWORD PTR [edi+656], eax
	mov DWORD PTR [edi+660], eax
	mov DWORD PTR [edi+664], eax
	mov DWORD PTR [edi+668], eax
	mov DWORD PTR [edi+672], eax
	mov DWORD PTR [edi+676], eax
	mov DWORD PTR [edi+680], eax
	mov DWORD PTR [edi+684], eax
	movzx eax, BYTE PTR [esi+56]
	mov DWORD PTR [edi+576], eax
	mov ebp, 56
22:
	sub ebp, 2
	mov edx, esi
	add edx, ebp
	movzx eax, BYTE PTR [edx]
	movzx edx, BYTE PTR [edx+1]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+16], eax
	mov ecx, DWORD PTR [edi+680]
	shr ecx, 14
	mov eax, DWORD PTR [edi+684]
	ror eax, 30
	add ecx, eax
	mov ebx, 0
	mov eax, 47885
	mul ecx
	add eax, DWORD PTR [edi+16]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+64], edx
	shr ebx, 16
	mov eax, 21671
	mul ecx
	add eax, DWORD PTR [edi+576]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+68], edx
	shr ebx, 16
	mov eax, 15725
	mul ecx
	add eax, DWORD PTR [edi+580]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+72], edx
	shr ebx, 16
	mov eax, 56455
	mul ecx
	add eax, DWORD PTR [edi+584]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+76], edx
	shr ebx, 16
	mov eax, 28842
	mul ecx
	add eax, DWORD PTR [edi+588]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+80], edx
	shr ebx, 16
	mov eax, 29242
	mul ecx
	add eax, DWORD PTR [edi+592]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+84], edx
	shr ebx, 16
	mov eax, 15757
	mul ecx
	add eax, DWORD PTR [edi+596]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+88], edx
	shr ebx, 16
	mov eax, 56979
	mul ecx
	add eax, DWORD PTR [edi+600]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+92], edx
	shr ebx, 16
	mov eax, 51567
	mul ecx
	add eax, DWORD PTR [edi+604]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+96], edx
	shr ebx, 16
	mov eax, 20777
	mul ecx
	add eax, DWORD PTR [edi+608]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+100], edx
	shr ebx, 16
	mov eax, 9398
	mul ecx
	add eax, DWORD PTR [edi+612]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+104], edx
	shr ebx, 16
	mov eax, 15281
	mul ecx
	add eax, DWORD PTR [edi+616]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+108], edx
	shr ebx, 16
	mov eax, 56342
	mul ecx
	add eax, DWORD PTR [edi+620]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+112], edx
	shr ebx, 16
	mov eax, 33589
	mul ecx
	add eax, DWORD PTR [edi+624]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+116], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+628]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+120], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+632]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+124], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+128], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+132], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+136], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+140], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+144], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+148], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+152], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+156], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+160], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+164], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+168], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+680]
	and eax, 16383
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+172], edx
	shr ebx, 16
	mov ebx, 0
	mov eax, DWORD PTR [edi+64]
	add eax, 47885
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+576], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+68]
	add eax, 21671
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+580], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+72]
	add eax, 15725
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+584], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+76]
	add eax, 56455
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+588], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+80]
	add eax, 28842
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+592], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+84]
	add eax, 29242
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+596], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+88]
	add eax, 15757
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+600], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+92]
	add eax, 56979
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+604], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+96]
	add eax, 51567
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+608], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+100]
	add eax, 20777
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+612], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+104]
	add eax, 9398
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+616], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+108]
	add eax, 15281
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+620], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+112]
	add eax, 56342
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+624], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+116]
	add eax, 33589
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+628], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+120]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+632], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+124]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+636], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+128]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+640], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+132]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+644], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+136]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+648], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+140]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+652], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+144]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+656], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+148]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+660], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+152]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+664], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+156]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+668], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+160]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+672], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+164]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+676], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+168]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+680], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+172]
	add eax, 49152
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+684], edx
	shr ebx, 16
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+576]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+580]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+584]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+588]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+592]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+596]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+600]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+604]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+608]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+612]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+616]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+620]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+624]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+628]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+632]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+636]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+640]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+644]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+648]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+652]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+656]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+660]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+664]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+156]
	mov edx, DWORD PTR [edi+668]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+672]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+676]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+680]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+684]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+684], eax
	cmp ebp, 0
	jne 22b
	mov eax, 0
	mov DWORD PTR [edi+3584], eax
	mov DWORD PTR [edi+3588], eax
	mov DWORD PTR [edi+3592], eax
	mov DWORD PTR [edi+3596], eax
	mov DWORD PTR [edi+3600], eax
	mov DWORD PTR [edi+3604], eax
	mov DWORD PTR [edi+3608], eax
	mov DWORD PTR [edi+3612], eax
	mov DWORD PTR [edi+3616], eax
	mov DWORD PTR [edi+3620], eax
	mov DWORD PTR [edi+3624], eax
	mov DWORD PTR [edi+3628], eax
	mov DWORD PTR [edi+3632], eax
	mov DWORD PTR [edi+3636], eax
	mov DWORD PTR [edi+3640], eax
	mov DWORD PTR [edi+3644], eax
	mov DWORD PTR [edi+3648], eax
	mov DWORD PTR [edi+3652], eax
	mov DWORD PTR [edi+3656], eax
	mov DWORD PTR [edi+3660], eax
	mov DWORD PTR [edi+3664], eax
	mov DWORD PTR [edi+3668], eax
	mov DWORD PTR [edi+3672], eax
	mov DWORD PTR [edi+3676], eax
	mov DWORD PTR [edi+3680], eax
	mov DWORD PTR [edi+3684], eax
	mov DWORD PTR [edi+3688], eax
	mov DWORD PTR [edi+3692], eax
	mov ebp, edi
23:
	mov ecx, DWORD PTR [ebp+320]
	mov ebx, 0
	mov eax, DWORD PTR [edi+448]
	mul ecx
	add eax, DWORD PTR [ebp+3584]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3584], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+452]
	mul ecx
	add eax, DWORD PTR [ebp+3588]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3588], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+456]
	mul ecx
	add eax, DWORD PTR [ebp+3592]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3592], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+460]
	mul ecx
	add eax, DWORD PTR [ebp+3596]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3596], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+464]
	mul ecx
	add eax, DWORD PTR [ebp+3600]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3600], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+468]
	mul ecx
	add eax, DWORD PTR [ebp+3604]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3604], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+472]
	mul ecx
	add eax, DWORD PTR [ebp+3608]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3608], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+476]
	mul ecx
	add eax, DWORD PTR [ebp+3612]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3612], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+480]
	mul ecx
	add eax, DWORD PTR [ebp+3616]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3616], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+484]
	mul ecx
	add eax, DWORD PTR [ebp+3620]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3620], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+488]
	mul ecx
	add eax, DWORD PTR [ebp+3624]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3624], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+492]
	mul ecx
	add eax, DWORD PTR [ebp+3628]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3628], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+496]
	mul ecx
	add eax, DWORD PTR [ebp+3632]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3632], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+500]
	mul ecx
	add eax, DWORD PTR [ebp+3636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3636], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+504]
	mul ecx
	add eax, DWORD PTR [ebp+3640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3640], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+508]
	mul ecx
	add eax, DWORD PTR [ebp+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+512]
	mul ecx
	add eax, DWORD PTR [ebp+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+516]
	mul ecx
	add eax, DWORD PTR [ebp+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+520]
	mul ecx
	add eax, DWORD PTR [ebp+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+524]
	mul ecx
	add eax, DWORD PTR [ebp+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+528]
	mul ecx
	add eax, DWORD PTR [ebp+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+532]
	mul ecx
	add eax, DWORD PTR [ebp+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+536]
	mul ecx
	add eax, DWORD PTR [ebp+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+540]
	mul ecx
	add eax, DWORD PTR [ebp+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+544]
	mul ecx
	add eax, DWORD PTR [ebp+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+548]
	mul ecx
	add eax, DWORD PTR [ebp+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+552]
	mul ecx
	add eax, DWORD PTR [ebp+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+556]
	mul ecx
	add eax, DWORD PTR [ebp+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+3692], edx
	shr ebx, 16
	mov DWORD PTR [ebp+3696], ebx
	add ebp, 4
	mov edx, edi
	add edx, 112
	cmp ebp, edx
	jne 23b
	mov eax, 0
	mov DWORD PTR [edi+192], eax
	mov DWORD PTR [edi+196], eax
	mov DWORD PTR [edi+200], eax
	mov DWORD PTR [edi+204], eax
	mov DWORD PTR [edi+208], eax
	mov DWORD PTR [edi+212], eax
	mov DWORD PTR [edi+216], eax
	mov DWORD PTR [edi+220], eax
	mov DWORD PTR [edi+224], eax
	mov DWORD PTR [edi+228], eax
	mov DWORD PTR [edi+232], eax
	mov DWORD PTR [edi+236], eax
	mov DWORD PTR [edi+240], eax
	mov DWORD PTR [edi+244], eax
	mov DWORD PTR [edi+248], eax
	mov DWORD PTR [edi+252], eax
	mov DWORD PTR [edi+256], eax
	mov DWORD PTR [edi+260], eax
	mov DWORD PTR [edi+264], eax
	mov DWORD PTR [edi+268], eax
	mov DWORD PTR [edi+272], eax
	mov DWORD PTR [edi+276], eax
	mov DWORD PTR [edi+280], eax
	mov DWORD PTR [edi+284], eax
	mov DWORD PTR [edi+288], eax
	mov DWORD PTR [edi+292], eax
	mov DWORD PTR [edi+296], eax
	mov DWORD PTR [edi+300], eax
	mov ebp, 224
24:
	sub ebp, 4
	mov edx, edi
	add edx, ebp
	mov eax, DWORD PTR [edx+3584]
	mov DWORD PTR [edi+16], eax
	mov ecx, DWORD PTR [edi+296]
	shr ecx, 14
	mov eax, DWORD PTR [edi+300]
	ror eax, 30
	add ecx, eax
	mov ebx, 0
	mov eax, 47885
	mul ecx
	add eax, DWORD PTR [edi+16]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+64], edx
	shr ebx, 16
	mov eax, 21671
	mul ecx
	add eax, DWORD PTR [edi+192]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+68], edx
	shr ebx, 16
	mov eax, 15725
	mul ecx
	add eax, DWORD PTR [edi+196]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+72], edx
	shr ebx, 16
	mov eax, 56455
	mul ecx
	add eax, DWORD PTR [edi+200]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+76], edx
	shr ebx, 16
	mov eax, 28842
	mul ecx
	add eax, DWORD PTR [edi+204]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+80], edx
	shr ebx, 16
	mov eax, 29242
	mul ecx
	add eax, DWORD PTR [edi+208]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+84], edx
	shr ebx, 16
	mov eax, 15757
	mul ecx
	add eax, DWORD PTR [edi+212]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+88], edx
	shr ebx, 16
	mov eax, 56979
	mul ecx
	add eax, DWORD PTR [edi+216]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+92], edx
	shr ebx, 16
	mov eax, 51567
	mul ecx
	add eax, DWORD PTR [edi+220]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+96], edx
	shr ebx, 16
	mov eax, 20777
	mul ecx
	add eax, DWORD PTR [edi+224]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+100], edx
	shr ebx, 16
	mov eax, 9398
	mul ecx
	add eax, DWORD PTR [edi+228]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+104], edx
	shr ebx, 16
	mov eax, 15281
	mul ecx
	add eax, DWORD PTR [edi+232]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+108], edx
	shr ebx, 16
	mov eax, 56342
	mul ecx
	add eax, DWORD PTR [edi+236]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+112], edx
	shr ebx, 16
	mov eax, 33589
	mul ecx
	add eax, DWORD PTR [edi+240]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+116], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+244]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+120], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+248]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+124], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+252]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+128], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+256]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+132], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+260]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+136], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+264]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+140], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+268]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+144], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+272]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+148], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+276]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+152], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+280]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+156], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+284]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+160], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+288]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+164], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+292]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+168], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+296]
	and eax, 16383
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+172], edx
	shr ebx, 16
	mov ebx, 0
	mov eax, DWORD PTR [edi+64]
	add eax, 47885
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+192], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+68]
	add eax, 21671
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+196], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+72]
	add eax, 15725
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+200], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+76]
	add eax, 56455
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+204], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+80]
	add eax, 28842
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+208], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+84]
	add eax, 29242
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+212], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+88]
	add eax, 15757
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+216], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+92]
	add eax, 56979
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+220], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+96]
	add eax, 51567
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+224], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+100]
	add eax, 20777
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+228], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+104]
	add eax, 9398
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+232], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+108]
	add eax, 15281
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+236], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+112]
	add eax, 56342
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+240], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+116]
	add eax, 33589
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+244], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+120]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+248], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+124]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+252], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+128]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+256], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+132]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+260], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+136]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+264], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+140]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+268], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+144]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+272], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+148]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+276], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+152]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+280], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+156]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+284], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+160]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+288], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+164]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+292], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+168]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+296], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+172]
	add eax, 49152
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+300], edx
	shr ebx, 16
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+192]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+196]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+200]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+204]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+208]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+212]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+216]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+220]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+224]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+228]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+232]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+236]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+240]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+244]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+248]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+252]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+256]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+260]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+156]
	mov edx, DWORD PTR [edi+284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+300], eax
	cmp ebp, 0
	jne 24b
	mov ebx, 0
	mov eax, DWORD PTR [edi+192]
	add eax, DWORD PTR [edi+576]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+64], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+196]
	add eax, DWORD PTR [edi+580]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+68], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+200]
	add eax, DWORD PTR [edi+584]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+72], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+204]
	add eax, DWORD PTR [edi+588]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+76], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+208]
	add eax, DWORD PTR [edi+592]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+80], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+212]
	add eax, DWORD PTR [edi+596]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+84], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+216]
	add eax, DWORD PTR [edi+600]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+88], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+220]
	add eax, DWORD PTR [edi+604]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+92], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+224]
	add eax, DWORD PTR [edi+608]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+96], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+228]
	add eax, DWORD PTR [edi+612]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+100], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+232]
	add eax, DWORD PTR [edi+616]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+104], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+236]
	add eax, DWORD PTR [edi+620]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+108], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+240]
	add eax, DWORD PTR [edi+624]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+112], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+244]
	add eax, DWORD PTR [edi+628]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+116], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+248]
	add eax, DWORD PTR [edi+632]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+120], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+252]
	add eax, DWORD PTR [edi+636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+124], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+256]
	add eax, DWORD PTR [edi+640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+128], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+260]
	add eax, DWORD PTR [edi+644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+132], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+264]
	add eax, DWORD PTR [edi+648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+136], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+268]
	add eax, DWORD PTR [edi+652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+140], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+272]
	add eax, DWORD PTR [edi+656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+144], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+276]
	add eax, DWORD PTR [edi+660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+148], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+280]
	add eax, DWORD PTR [edi+664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+152], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+284]
	add eax, DWORD PTR [edi+668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+156], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+288]
	add eax, DWORD PTR [edi+672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+160], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+292]
	add eax, DWORD PTR [edi+676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+164], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+296]
	add eax, DWORD PTR [edi+680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+168], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+300]
	add eax, DWORD PTR [edi+684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+172], edx
	shr ebx, 16
	mov ebx, 0
	mov eax, DWORD PTR [edi+64]
	add eax, 47885
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+192], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+68]
	add eax, 21671
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+196], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+72]
	add eax, 15725
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+200], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+76]
	add eax, 56455
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+204], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+80]
	add eax, 28842
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+208], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+84]
	add eax, 29242
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+212], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+88]
	add eax, 15757
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+216], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+92]
	add eax, 56979
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+220], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+96]
	add eax, 51567
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+224], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+100]
	add eax, 20777
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+228], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+104]
	add eax, 9398
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+232], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+108]
	add eax, 15281
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+236], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+112]
	add eax, 56342
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+240], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+116]
	add eax, 33589
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+244], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+120]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+248], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+124]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+252], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+128]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+256], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+132]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+260], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+136]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+264], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+140]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+268], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+144]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+272], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+148]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+276], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+152]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+280], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+156]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+284], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+160]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+288], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+164]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+292], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+168]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+296], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+172]
	add eax, 49152
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+300], edx
	shr ebx, 16
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+192]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+196]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+200]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+204]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+208]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+212]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+216]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+220]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+224]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+228]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+232]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+236]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+240]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+244]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+248]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+252]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+256]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+260]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+156]
	mov edx, DWORD PTR [edi+284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+300], eax
	mov esi, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+192]
	mov BYTE PTR [esi], al
	shr eax, 8
	mov BYTE PTR [esi+1], al
	mov eax, DWORD PTR [edi+196]
	mov BYTE PTR [esi+2], al
	shr eax, 8
	mov BYTE PTR [esi+3], al
	mov eax, DWORD PTR [edi+200]
	mov BYTE PTR [esi+4], al
	shr eax, 8
	mov BYTE PTR [esi+5], al
	mov eax, DWORD PTR [edi+204]
	mov BYTE PTR [esi+6], al
	shr eax, 8
	mov BYTE PTR [esi+7], al
	mov eax, DWORD PTR [edi+208]
	mov BYTE PTR [esi+8], al
	shr eax, 8
	mov BYTE PTR [esi+9], al
	mov eax, DWORD PTR [edi+212]
	mov BYTE PTR [esi+10], al
	shr eax, 8
	mov BYTE PTR [esi+11], al
	mov eax, DWORD PTR [edi+216]
	mov BYTE PTR [esi+12], al
	shr eax, 8
	mov BYTE PTR [esi+13], al
	mov eax, DWORD PTR [edi+220]
	mov BYTE PTR [esi+14], al
	shr eax, 8
	mov BYTE PTR [esi+15], al
	mov eax, DWORD PTR [edi+224]
	mov BYTE PTR [esi+16], al
	shr eax, 8
	mov BYTE PTR [esi+17], al
	mov eax, DWORD PTR [edi+228]
	mov BYTE PTR [esi+18], al
	shr eax, 8
	mov BYTE PTR [esi+19], al
	mov eax, DWORD PTR [edi+232]
	mov BYTE PTR [esi+20], al
	shr eax, 8
	mov BYTE PTR [esi+21], al
	mov eax, DWORD PTR [edi+236]
	mov BYTE PTR [esi+22], al
	shr eax, 8
	mov BYTE PTR [esi+23], al
	mov eax, DWORD PTR [edi+240]
	mov BYTE PTR [esi+24], al
	shr eax, 8
	mov BYTE PTR [esi+25], al
	mov eax, DWORD PTR [edi+244]
	mov BYTE PTR [esi+26], al
	shr eax, 8
	mov BYTE PTR [esi+27], al
	mov eax, DWORD PTR [edi+248]
	mov BYTE PTR [esi+28], al
	shr eax, 8
	mov BYTE PTR [esi+29], al
	mov eax, DWORD PTR [edi+252]
	mov BYTE PTR [esi+30], al
	shr eax, 8
	mov BYTE PTR [esi+31], al
	mov eax, DWORD PTR [edi+256]
	mov BYTE PTR [esi+32], al
	shr eax, 8
	mov BYTE PTR [esi+33], al
	mov eax, DWORD PTR [edi+260]
	mov BYTE PTR [esi+34], al
	shr eax, 8
	mov BYTE PTR [esi+35], al
	mov eax, DWORD PTR [edi+264]
	mov BYTE PTR [esi+36], al
	shr eax, 8
	mov BYTE PTR [esi+37], al
	mov eax, DWORD PTR [edi+268]
	mov BYTE PTR [esi+38], al
	shr eax, 8
	mov BYTE PTR [esi+39], al
	mov eax, DWORD PTR [edi+272]
	mov BYTE PTR [esi+40], al
	shr eax, 8
	mov BYTE PTR [esi+41], al
	mov eax, DWORD PTR [edi+276]
	mov BYTE PTR [esi+42], al
	shr eax, 8
	mov BYTE PTR [esi+43], al
	mov eax, DWORD PTR [edi+280]
	mov BYTE PTR [esi+44], al
	shr eax, 8
	mov BYTE PTR [esi+45], al
	mov eax, DWORD PTR [edi+284]
	mov BYTE PTR [esi+46], al
	shr eax, 8
	mov BYTE PTR [esi+47], al
	mov eax, DWORD PTR [edi+288]
	mov BYTE PTR [esi+48], al
	shr eax, 8
	mov BYTE PTR [esi+49], al
	mov eax, DWORD PTR [edi+292]
	mov BYTE PTR [esi+50], al
	shr eax, 8
	mov BYTE PTR [esi+51], al
	mov eax, DWORD PTR [edi+296]
	mov BYTE PTR [esi+52], al
	shr eax, 8
	mov BYTE PTR [esi+53], al
	mov eax, DWORD PTR [edi+300]
	mov BYTE PTR [esi+54], al
	shr eax, 8
	mov BYTE PTR [esi+55], al
	mov eax, 0
	mov BYTE PTR [esi+56], al
	mov eax, edi
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov ebp, DWORD PTR [eax+12]
	mov edi, DWORD PTR [eax+8]
	ret
	.p2align 6

vg_ed448_scalar_base:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebp, edi
	add ebp, 64
	mov ebx, 0
	mov eax, 704
20:
	mov DWORD PTR [ebp], ebx
	add ebp, 4
	sub eax, 1
	jne 20b
	mov ebp, edi
	add ebp, 64
	mov eax, 1
	mov DWORD PTR [ebp+128], eax
	mov eax, 1
	mov DWORD PTR [ebp+256], eax
	mov eax, 49246
	mov DWORD PTR [ebp+1024], eax
	mov eax, 50956
	mov DWORD PTR [ebp+1028], eax
	mov eax, 43051
	mov DWORD PTR [ebp+1032], eax
	mov eax, 9766
	mov DWORD PTR [ebp+1036], eax
	mov eax, 37774
	mov DWORD PTR [ebp+1040], eax
	mov eax, 35584
	mov DWORD PTR [ebp+1044], eax
	mov eax, 32993
	mov DWORD PTR [ebp+1048], eax
	mov eax, 17211
	mov DWORD PTR [ebp+1052], eax
	mov eax, 25873
	mov DWORD PTR [ebp+1056], eax
	mov eax, 10934
	mov DWORD PTR [ebp+1060], eax
	mov eax, 6903
	mov DWORD PTR [ebp+1064], eax
	mov eax, 4782
	mov DWORD PTR [ebp+1068], eax
	mov eax, 42084
	mov DWORD PTR [ebp+1072], eax
	mov eax, 41939
	mov DWORD PTR [ebp+1076], eax
	mov eax, 58148
	mov DWORD PTR [ebp+1080], eax
	mov eax, 60013
	mov DWORD PTR [ebp+1084], eax
	mov eax, 5991
	mov DWORD PTR [ebp+1088], eax
	mov eax, 18191
	mov DWORD PTR [ebp+1092], eax
	mov eax, 25968
	mov DWORD PTR [ebp+1096], eax
	mov eax, 40468
	mov DWORD PTR [ebp+1100], eax
	mov eax, 14042
	mov DWORD PTR [ebp+1104], eax
	mov eax, 8895
	mov DWORD PTR [ebp+1108], eax
	mov eax, 5542
	mov DWORD PTR [ebp+1112], eax
	mov eax, 8733
	mov DWORD PTR [ebp+1116], eax
	mov eax, 3565
	mov DWORD PTR [ebp+1120], eax
	mov eax, 27629
	mov DWORD PTR [ebp+1124], eax
	mov eax, 28870
	mov DWORD PTR [ebp+1128], eax
	mov eax, 20249
	mov DWORD PTR [ebp+1132], eax
	mov eax, 64020
	mov DWORD PTR [ebp+1152], eax
	mov eax, 62000
	mov DWORD PTR [ebp+1156], eax
	mov eax, 31067
	mov DWORD PTR [ebp+1160], eax
	mov eax, 38920
	mov DWORD PTR [ebp+1164], eax
	mov eax, 51373
	mov DWORD PTR [ebp+1168], eax
	mov eax, 20183
	mov DWORD PTR [ebp+1172], eax
	mov eax, 4908
	mov DWORD PTR [ebp+1176], eax
	mov eax, 64957
	mov DWORD PTR [ebp+1180], eax
	mov eax, 14788
	mov DWORD PTR [ebp+1184], eax
	mov eax, 59004
	mov DWORD PTR [ebp+1188], eax
	mov eax, 65308
	mov DWORD PTR [ebp+1192], eax
	mov eax, 15059
	mov DWORD PTR [ebp+1196], eax
	mov eax, 49879
	mov DWORD PTR [ebp+1200], eax
	mov eax, 1440
	mov DWORD PTR [ebp+1204], eax
	mov eax, 39966
	mov DWORD PTR [ebp+1208], eax
	mov eax, 34680
	mov DWORD PTR [ebp+1212], eax
	mov eax, 38976
	mov DWORD PTR [ebp+1216], eax
	mov eax, 27811
	mov DWORD PTR [ebp+1220], eax
	mov eax, 29555
	mov DWORD PTR [ebp+1224], eax
	mov eax, 19434
	mov DWORD PTR [ebp+1228], eax
	mov eax, 51042
	mov DWORD PTR [ebp+1232], eax
	mov eax, 22217
	mov DWORD PTR [ebp+1236], eax
	mov eax, 8247
	mov DWORD PTR [ebp+1240], eax
	mov eax, 34934
	mov DWORD PTR [ebp+1244], eax
	mov eax, 48164
	mov DWORD PTR [ebp+1248], eax
	mov eax, 28342
	mov DWORD PTR [ebp+1252], eax
	mov eax, 18033
	mov DWORD PTR [ebp+1256], eax
	mov eax, 26943
	mov DWORD PTR [ebp+1260], eax
	mov eax, 1
	mov DWORD PTR [ebp+1280], eax
	mov eax, 26454
	mov DWORD PTR [ebp+1408], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1412], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1416], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1420], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1424], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1428], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1432], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1436], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1440], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1444], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1448], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1452], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1456], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1460], eax
	mov eax, 65534
	mov DWORD PTR [ebp+1464], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1468], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1472], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1476], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1480], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1484], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1488], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1492], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1496], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1500], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1504], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1508], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1512], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1516], eax
	mov esi, DWORD PTR [esp+8]
	mov ebp, edi
	mov ecx, 57
21:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebp+3072], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebp+3073], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebp+3074], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebp+3075], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebp+3076], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebp+3077], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebp+3078], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebp+3079], dl
	add esi, 1
	add ebp, 8
	sub ecx, 1
	jne 21b
	mov esi, 456
22:
	sub esi, 1
	mov eax, 1600
	mov ecx, 64
	mov edx, 192
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 64
	mov edx, 64
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 192
	mov edx, 192
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 320
	mov edx, 320
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 2112
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 1600
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 64
	mov ecx, 2368
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 192
	mov ecx, 1984
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 320
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 320
	mov edx, 1344
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1600
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 64
	mov edx, 1088
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 192
	mov edx, 1216
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 1472
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 2112
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 1728
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 1728
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 64
	mov edx, 192
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 1088
	mov edx, 1216
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 1600
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 1600
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 1984
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 2240
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, edi
	add ebp, esi
	movzx eax, BYTE PTR [ebp+3072]
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [edi+64]
	mov ecx, DWORD PTR [edi+448]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+64], eax
	mov DWORD PTR [edi+448], ecx
	mov eax, DWORD PTR [edi+68]
	mov ecx, DWORD PTR [edi+452]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+68], eax
	mov DWORD PTR [edi+452], ecx
	mov eax, DWORD PTR [edi+72]
	mov ecx, DWORD PTR [edi+456]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+72], eax
	mov DWORD PTR [edi+456], ecx
	mov eax, DWORD PTR [edi+76]
	mov ecx, DWORD PTR [edi+460]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+76], eax
	mov DWORD PTR [edi+460], ecx
	mov eax, DWORD PTR [edi+80]
	mov ecx, DWORD PTR [edi+464]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+80], eax
	mov DWORD PTR [edi+464], ecx
	mov eax, DWORD PTR [edi+84]
	mov ecx, DWORD PTR [edi+468]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+84], eax
	mov DWORD PTR [edi+468], ecx
	mov eax, DWORD PTR [edi+88]
	mov ecx, DWORD PTR [edi+472]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+88], eax
	mov DWORD PTR [edi+472], ecx
	mov eax, DWORD PTR [edi+92]
	mov ecx, DWORD PTR [edi+476]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+92], eax
	mov DWORD PTR [edi+476], ecx
	mov eax, DWORD PTR [edi+96]
	mov ecx, DWORD PTR [edi+480]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+96], eax
	mov DWORD PTR [edi+480], ecx
	mov eax, DWORD PTR [edi+100]
	mov ecx, DWORD PTR [edi+484]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+100], eax
	mov DWORD PTR [edi+484], ecx
	mov eax, DWORD PTR [edi+104]
	mov ecx, DWORD PTR [edi+488]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+104], eax
	mov DWORD PTR [edi+488], ecx
	mov eax, DWORD PTR [edi+108]
	mov ecx, DWORD PTR [edi+492]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+108], eax
	mov DWORD PTR [edi+492], ecx
	mov eax, DWORD PTR [edi+112]
	mov ecx, DWORD PTR [edi+496]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+112], eax
	mov DWORD PTR [edi+496], ecx
	mov eax, DWORD PTR [edi+116]
	mov ecx, DWORD PTR [edi+500]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+116], eax
	mov DWORD PTR [edi+500], ecx
	mov eax, DWORD PTR [edi+120]
	mov ecx, DWORD PTR [edi+504]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+120], eax
	mov DWORD PTR [edi+504], ecx
	mov eax, DWORD PTR [edi+124]
	mov ecx, DWORD PTR [edi+508]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+124], eax
	mov DWORD PTR [edi+508], ecx
	mov eax, DWORD PTR [edi+128]
	mov ecx, DWORD PTR [edi+512]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+128], eax
	mov DWORD PTR [edi+512], ecx
	mov eax, DWORD PTR [edi+132]
	mov ecx, DWORD PTR [edi+516]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+132], eax
	mov DWORD PTR [edi+516], ecx
	mov eax, DWORD PTR [edi+136]
	mov ecx, DWORD PTR [edi+520]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+136], eax
	mov DWORD PTR [edi+520], ecx
	mov eax, DWORD PTR [edi+140]
	mov ecx, DWORD PTR [edi+524]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+140], eax
	mov DWORD PTR [edi+524], ecx
	mov eax, DWORD PTR [edi+144]
	mov ecx, DWORD PTR [edi+528]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+144], eax
	mov DWORD PTR [edi+528], ecx
	mov eax, DWORD PTR [edi+148]
	mov ecx, DWORD PTR [edi+532]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+148], eax
	mov DWORD PTR [edi+532], ecx
	mov eax, DWORD PTR [edi+152]
	mov ecx, DWORD PTR [edi+536]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+152], eax
	mov DWORD PTR [edi+536], ecx
	mov eax, DWORD PTR [edi+156]
	mov ecx, DWORD PTR [edi+540]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+156], eax
	mov DWORD PTR [edi+540], ecx
	mov eax, DWORD PTR [edi+160]
	mov ecx, DWORD PTR [edi+544]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+160], eax
	mov DWORD PTR [edi+544], ecx
	mov eax, DWORD PTR [edi+164]
	mov ecx, DWORD PTR [edi+548]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+164], eax
	mov DWORD PTR [edi+548], ecx
	mov eax, DWORD PTR [edi+168]
	mov ecx, DWORD PTR [edi+552]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+168], eax
	mov DWORD PTR [edi+552], ecx
	mov eax, DWORD PTR [edi+172]
	mov ecx, DWORD PTR [edi+556]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+172], eax
	mov DWORD PTR [edi+556], ecx
	mov eax, DWORD PTR [edi+192]
	mov ecx, DWORD PTR [edi+576]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+192], eax
	mov DWORD PTR [edi+576], ecx
	mov eax, DWORD PTR [edi+196]
	mov ecx, DWORD PTR [edi+580]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+196], eax
	mov DWORD PTR [edi+580], ecx
	mov eax, DWORD PTR [edi+200]
	mov ecx, DWORD PTR [edi+584]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+200], eax
	mov DWORD PTR [edi+584], ecx
	mov eax, DWORD PTR [edi+204]
	mov ecx, DWORD PTR [edi+588]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+204], eax
	mov DWORD PTR [edi+588], ecx
	mov eax, DWORD PTR [edi+208]
	mov ecx, DWORD PTR [edi+592]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+208], eax
	mov DWORD PTR [edi+592], ecx
	mov eax, DWORD PTR [edi+212]
	mov ecx, DWORD PTR [edi+596]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+212], eax
	mov DWORD PTR [edi+596], ecx
	mov eax, DWORD PTR [edi+216]
	mov ecx, DWORD PTR [edi+600]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+216], eax
	mov DWORD PTR [edi+600], ecx
	mov eax, DWORD PTR [edi+220]
	mov ecx, DWORD PTR [edi+604]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+220], eax
	mov DWORD PTR [edi+604], ecx
	mov eax, DWORD PTR [edi+224]
	mov ecx, DWORD PTR [edi+608]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+224], eax
	mov DWORD PTR [edi+608], ecx
	mov eax, DWORD PTR [edi+228]
	mov ecx, DWORD PTR [edi+612]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+228], eax
	mov DWORD PTR [edi+612], ecx
	mov eax, DWORD PTR [edi+232]
	mov ecx, DWORD PTR [edi+616]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+232], eax
	mov DWORD PTR [edi+616], ecx
	mov eax, DWORD PTR [edi+236]
	mov ecx, DWORD PTR [edi+620]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+236], eax
	mov DWORD PTR [edi+620], ecx
	mov eax, DWORD PTR [edi+240]
	mov ecx, DWORD PTR [edi+624]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+240], eax
	mov DWORD PTR [edi+624], ecx
	mov eax, DWORD PTR [edi+244]
	mov ecx, DWORD PTR [edi+628]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+244], eax
	mov DWORD PTR [edi+628], ecx
	mov eax, DWORD PTR [edi+248]
	mov ecx, DWORD PTR [edi+632]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+248], eax
	mov DWORD PTR [edi+632], ecx
	mov eax, DWORD PTR [edi+252]
	mov ecx, DWORD PTR [edi+636]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+252], eax
	mov DWORD PTR [edi+636], ecx
	mov eax, DWORD PTR [edi+256]
	mov ecx, DWORD PTR [edi+640]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+256], eax
	mov DWORD PTR [edi+640], ecx
	mov eax, DWORD PTR [edi+260]
	mov ecx, DWORD PTR [edi+644]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+260], eax
	mov DWORD PTR [edi+644], ecx
	mov eax, DWORD PTR [edi+264]
	mov ecx, DWORD PTR [edi+648]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+264], eax
	mov DWORD PTR [edi+648], ecx
	mov eax, DWORD PTR [edi+268]
	mov ecx, DWORD PTR [edi+652]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+268], eax
	mov DWORD PTR [edi+652], ecx
	mov eax, DWORD PTR [edi+272]
	mov ecx, DWORD PTR [edi+656]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+272], eax
	mov DWORD PTR [edi+656], ecx
	mov eax, DWORD PTR [edi+276]
	mov ecx, DWORD PTR [edi+660]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+276], eax
	mov DWORD PTR [edi+660], ecx
	mov eax, DWORD PTR [edi+280]
	mov ecx, DWORD PTR [edi+664]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+280], eax
	mov DWORD PTR [edi+664], ecx
	mov eax, DWORD PTR [edi+284]
	mov ecx, DWORD PTR [edi+668]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+284], eax
	mov DWORD PTR [edi+668], ecx
	mov eax, DWORD PTR [edi+288]
	mov ecx, DWORD PTR [edi+672]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+288], eax
	mov DWORD PTR [edi+672], ecx
	mov eax, DWORD PTR [edi+292]
	mov ecx, DWORD PTR [edi+676]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+292], eax
	mov DWORD PTR [edi+676], ecx
	mov eax, DWORD PTR [edi+296]
	mov ecx, DWORD PTR [edi+680]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+296], eax
	mov DWORD PTR [edi+680], ecx
	mov eax, DWORD PTR [edi+300]
	mov ecx, DWORD PTR [edi+684]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+300], eax
	mov DWORD PTR [edi+684], ecx
	mov eax, DWORD PTR [edi+320]
	mov ecx, DWORD PTR [edi+704]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+320], eax
	mov DWORD PTR [edi+704], ecx
	mov eax, DWORD PTR [edi+324]
	mov ecx, DWORD PTR [edi+708]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+324], eax
	mov DWORD PTR [edi+708], ecx
	mov eax, DWORD PTR [edi+328]
	mov ecx, DWORD PTR [edi+712]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+328], eax
	mov DWORD PTR [edi+712], ecx
	mov eax, DWORD PTR [edi+332]
	mov ecx, DWORD PTR [edi+716]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+332], eax
	mov DWORD PTR [edi+716], ecx
	mov eax, DWORD PTR [edi+336]
	mov ecx, DWORD PTR [edi+720]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+336], eax
	mov DWORD PTR [edi+720], ecx
	mov eax, DWORD PTR [edi+340]
	mov ecx, DWORD PTR [edi+724]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+340], eax
	mov DWORD PTR [edi+724], ecx
	mov eax, DWORD PTR [edi+344]
	mov ecx, DWORD PTR [edi+728]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+344], eax
	mov DWORD PTR [edi+728], ecx
	mov eax, DWORD PTR [edi+348]
	mov ecx, DWORD PTR [edi+732]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+348], eax
	mov DWORD PTR [edi+732], ecx
	mov eax, DWORD PTR [edi+352]
	mov ecx, DWORD PTR [edi+736]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+352], eax
	mov DWORD PTR [edi+736], ecx
	mov eax, DWORD PTR [edi+356]
	mov ecx, DWORD PTR [edi+740]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+356], eax
	mov DWORD PTR [edi+740], ecx
	mov eax, DWORD PTR [edi+360]
	mov ecx, DWORD PTR [edi+744]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+360], eax
	mov DWORD PTR [edi+744], ecx
	mov eax, DWORD PTR [edi+364]
	mov ecx, DWORD PTR [edi+748]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+364], eax
	mov DWORD PTR [edi+748], ecx
	mov eax, DWORD PTR [edi+368]
	mov ecx, DWORD PTR [edi+752]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+368], eax
	mov DWORD PTR [edi+752], ecx
	mov eax, DWORD PTR [edi+372]
	mov ecx, DWORD PTR [edi+756]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+372], eax
	mov DWORD PTR [edi+756], ecx
	mov eax, DWORD PTR [edi+376]
	mov ecx, DWORD PTR [edi+760]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+376], eax
	mov DWORD PTR [edi+760], ecx
	mov eax, DWORD PTR [edi+380]
	mov ecx, DWORD PTR [edi+764]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+380], eax
	mov DWORD PTR [edi+764], ecx
	mov eax, DWORD PTR [edi+384]
	mov ecx, DWORD PTR [edi+768]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+384], eax
	mov DWORD PTR [edi+768], ecx
	mov eax, DWORD PTR [edi+388]
	mov ecx, DWORD PTR [edi+772]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+388], eax
	mov DWORD PTR [edi+772], ecx
	mov eax, DWORD PTR [edi+392]
	mov ecx, DWORD PTR [edi+776]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+392], eax
	mov DWORD PTR [edi+776], ecx
	mov eax, DWORD PTR [edi+396]
	mov ecx, DWORD PTR [edi+780]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+396], eax
	mov DWORD PTR [edi+780], ecx
	mov eax, DWORD PTR [edi+400]
	mov ecx, DWORD PTR [edi+784]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+400], eax
	mov DWORD PTR [edi+784], ecx
	mov eax, DWORD PTR [edi+404]
	mov ecx, DWORD PTR [edi+788]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+404], eax
	mov DWORD PTR [edi+788], ecx
	mov eax, DWORD PTR [edi+408]
	mov ecx, DWORD PTR [edi+792]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+792], ecx
	mov eax, DWORD PTR [edi+412]
	mov ecx, DWORD PTR [edi+796]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+412], eax
	mov DWORD PTR [edi+796], ecx
	mov eax, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [edi+800]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+800], ecx
	mov eax, DWORD PTR [edi+420]
	mov ecx, DWORD PTR [edi+804]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+420], eax
	mov DWORD PTR [edi+804], ecx
	mov eax, DWORD PTR [edi+424]
	mov ecx, DWORD PTR [edi+808]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+808], ecx
	mov eax, DWORD PTR [edi+428]
	mov ecx, DWORD PTR [edi+812]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+428], eax
	mov DWORD PTR [edi+812], ecx
	cmp esi, 0
	jne 22b
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+1856], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+1860], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+1864], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+1868], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+1872], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+1876], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+1880], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+1884], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+1888], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+1892], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+1896], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+1900], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+1904], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+1908], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+1912], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+1916], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+1920], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+1924], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+1928], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+1932], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+1936], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+1940], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+1944], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+1948], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+1952], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+1956], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+1960], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+1964], eax
	mov esi, 1
23:
	mov eax, 1856
	mov ecx, 1856
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 23b
	mov eax, 1856
	mov ecx, 1856
	mov edx, 320
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1856]
	mov DWORD PTR [edi+1984], eax
	mov eax, DWORD PTR [edi+1860]
	mov DWORD PTR [edi+1988], eax
	mov eax, DWORD PTR [edi+1864]
	mov DWORD PTR [edi+1992], eax
	mov eax, DWORD PTR [edi+1868]
	mov DWORD PTR [edi+1996], eax
	mov eax, DWORD PTR [edi+1872]
	mov DWORD PTR [edi+2000], eax
	mov eax, DWORD PTR [edi+1876]
	mov DWORD PTR [edi+2004], eax
	mov eax, DWORD PTR [edi+1880]
	mov DWORD PTR [edi+2008], eax
	mov eax, DWORD PTR [edi+1884]
	mov DWORD PTR [edi+2012], eax
	mov eax, DWORD PTR [edi+1888]
	mov DWORD PTR [edi+2016], eax
	mov eax, DWORD PTR [edi+1892]
	mov DWORD PTR [edi+2020], eax
	mov eax, DWORD PTR [edi+1896]
	mov DWORD PTR [edi+2024], eax
	mov eax, DWORD PTR [edi+1900]
	mov DWORD PTR [edi+2028], eax
	mov eax, DWORD PTR [edi+1904]
	mov DWORD PTR [edi+2032], eax
	mov eax, DWORD PTR [edi+1908]
	mov DWORD PTR [edi+2036], eax
	mov eax, DWORD PTR [edi+1912]
	mov DWORD PTR [edi+2040], eax
	mov eax, DWORD PTR [edi+1916]
	mov DWORD PTR [edi+2044], eax
	mov eax, DWORD PTR [edi+1920]
	mov DWORD PTR [edi+2048], eax
	mov eax, DWORD PTR [edi+1924]
	mov DWORD PTR [edi+2052], eax
	mov eax, DWORD PTR [edi+1928]
	mov DWORD PTR [edi+2056], eax
	mov eax, DWORD PTR [edi+1932]
	mov DWORD PTR [edi+2060], eax
	mov eax, DWORD PTR [edi+1936]
	mov DWORD PTR [edi+2064], eax
	mov eax, DWORD PTR [edi+1940]
	mov DWORD PTR [edi+2068], eax
	mov eax, DWORD PTR [edi+1944]
	mov DWORD PTR [edi+2072], eax
	mov eax, DWORD PTR [edi+1948]
	mov DWORD PTR [edi+2076], eax
	mov eax, DWORD PTR [edi+1952]
	mov DWORD PTR [edi+2080], eax
	mov eax, DWORD PTR [edi+1956]
	mov DWORD PTR [edi+2084], eax
	mov eax, DWORD PTR [edi+1960]
	mov DWORD PTR [edi+2088], eax
	mov eax, DWORD PTR [edi+1964]
	mov DWORD PTR [edi+2092], eax
	mov esi, 2
24:
	mov eax, 1984
	mov ecx, 1984
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 24b
	mov eax, 1984
	mov ecx, 1984
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1984]
	mov DWORD PTR [edi+2112], eax
	mov eax, DWORD PTR [edi+1988]
	mov DWORD PTR [edi+2116], eax
	mov eax, DWORD PTR [edi+1992]
	mov DWORD PTR [edi+2120], eax
	mov eax, DWORD PTR [edi+1996]
	mov DWORD PTR [edi+2124], eax
	mov eax, DWORD PTR [edi+2000]
	mov DWORD PTR [edi+2128], eax
	mov eax, DWORD PTR [edi+2004]
	mov DWORD PTR [edi+2132], eax
	mov eax, DWORD PTR [edi+2008]
	mov DWORD PTR [edi+2136], eax
	mov eax, DWORD PTR [edi+2012]
	mov DWORD PTR [edi+2140], eax
	mov eax, DWORD PTR [edi+2016]
	mov DWORD PTR [edi+2144], eax
	mov eax, DWORD PTR [edi+2020]
	mov DWORD PTR [edi+2148], eax
	mov eax, DWORD PTR [edi+2024]
	mov DWORD PTR [edi+2152], eax
	mov eax, DWORD PTR [edi+2028]
	mov DWORD PTR [edi+2156], eax
	mov eax, DWORD PTR [edi+2032]
	mov DWORD PTR [edi+2160], eax
	mov eax, DWORD PTR [edi+2036]
	mov DWORD PTR [edi+2164], eax
	mov eax, DWORD PTR [edi+2040]
	mov DWORD PTR [edi+2168], eax
	mov eax, DWORD PTR [edi+2044]
	mov DWORD PTR [edi+2172], eax
	mov eax, DWORD PTR [edi+2048]
	mov DWORD PTR [edi+2176], eax
	mov eax, DWORD PTR [edi+2052]
	mov DWORD PTR [edi+2180], eax
	mov eax, DWORD PTR [edi+2056]
	mov DWORD PTR [edi+2184], eax
	mov eax, DWORD PTR [edi+2060]
	mov DWORD PTR [edi+2188], eax
	mov eax, DWORD PTR [edi+2064]
	mov DWORD PTR [edi+2192], eax
	mov eax, DWORD PTR [edi+2068]
	mov DWORD PTR [edi+2196], eax
	mov eax, DWORD PTR [edi+2072]
	mov DWORD PTR [edi+2200], eax
	mov eax, DWORD PTR [edi+2076]
	mov DWORD PTR [edi+2204], eax
	mov eax, DWORD PTR [edi+2080]
	mov DWORD PTR [edi+2208], eax
	mov eax, DWORD PTR [edi+2084]
	mov DWORD PTR [edi+2212], eax
	mov eax, DWORD PTR [edi+2088]
	mov DWORD PTR [edi+2216], eax
	mov eax, DWORD PTR [edi+2092]
	mov DWORD PTR [edi+2220], eax
	mov esi, 4
25:
	mov eax, 2112
	mov ecx, 2112
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 25b
	mov eax, 2112
	mov ecx, 2112
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2112]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2116]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2120]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2124]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2128]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2132]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2136]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2140]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2144]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2148]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2300], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2304], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2308], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2312], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2316], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2320], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2324], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2328], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2332], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2336], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2340], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2344], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2348], eax
	mov esi, 8
26:
	mov eax, 2240
	mov ecx, 2240
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 26b
	mov eax, 2240
	mov ecx, 2240
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2240]
	mov DWORD PTR [edi+2368], eax
	mov eax, DWORD PTR [edi+2244]
	mov DWORD PTR [edi+2372], eax
	mov eax, DWORD PTR [edi+2248]
	mov DWORD PTR [edi+2376], eax
	mov eax, DWORD PTR [edi+2252]
	mov DWORD PTR [edi+2380], eax
	mov eax, DWORD PTR [edi+2256]
	mov DWORD PTR [edi+2384], eax
	mov eax, DWORD PTR [edi+2260]
	mov DWORD PTR [edi+2388], eax
	mov eax, DWORD PTR [edi+2264]
	mov DWORD PTR [edi+2392], eax
	mov eax, DWORD PTR [edi+2268]
	mov DWORD PTR [edi+2396], eax
	mov eax, DWORD PTR [edi+2272]
	mov DWORD PTR [edi+2400], eax
	mov eax, DWORD PTR [edi+2276]
	mov DWORD PTR [edi+2404], eax
	mov eax, DWORD PTR [edi+2280]
	mov DWORD PTR [edi+2408], eax
	mov eax, DWORD PTR [edi+2284]
	mov DWORD PTR [edi+2412], eax
	mov eax, DWORD PTR [edi+2288]
	mov DWORD PTR [edi+2416], eax
	mov eax, DWORD PTR [edi+2292]
	mov DWORD PTR [edi+2420], eax
	mov eax, DWORD PTR [edi+2296]
	mov DWORD PTR [edi+2424], eax
	mov eax, DWORD PTR [edi+2300]
	mov DWORD PTR [edi+2428], eax
	mov eax, DWORD PTR [edi+2304]
	mov DWORD PTR [edi+2432], eax
	mov eax, DWORD PTR [edi+2308]
	mov DWORD PTR [edi+2436], eax
	mov eax, DWORD PTR [edi+2312]
	mov DWORD PTR [edi+2440], eax
	mov eax, DWORD PTR [edi+2316]
	mov DWORD PTR [edi+2444], eax
	mov eax, DWORD PTR [edi+2320]
	mov DWORD PTR [edi+2448], eax
	mov eax, DWORD PTR [edi+2324]
	mov DWORD PTR [edi+2452], eax
	mov eax, DWORD PTR [edi+2328]
	mov DWORD PTR [edi+2456], eax
	mov eax, DWORD PTR [edi+2332]
	mov DWORD PTR [edi+2460], eax
	mov eax, DWORD PTR [edi+2336]
	mov DWORD PTR [edi+2464], eax
	mov eax, DWORD PTR [edi+2340]
	mov DWORD PTR [edi+2468], eax
	mov eax, DWORD PTR [edi+2344]
	mov DWORD PTR [edi+2472], eax
	mov eax, DWORD PTR [edi+2348]
	mov DWORD PTR [edi+2476], eax
	mov esi, 16
27:
	mov eax, 2368
	mov ecx, 2368
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 27b
	mov eax, 2368
	mov ecx, 2368
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2368]
	mov DWORD PTR [edi+2496], eax
	mov eax, DWORD PTR [edi+2372]
	mov DWORD PTR [edi+2500], eax
	mov eax, DWORD PTR [edi+2376]
	mov DWORD PTR [edi+2504], eax
	mov eax, DWORD PTR [edi+2380]
	mov DWORD PTR [edi+2508], eax
	mov eax, DWORD PTR [edi+2384]
	mov DWORD PTR [edi+2512], eax
	mov eax, DWORD PTR [edi+2388]
	mov DWORD PTR [edi+2516], eax
	mov eax, DWORD PTR [edi+2392]
	mov DWORD PTR [edi+2520], eax
	mov eax, DWORD PTR [edi+2396]
	mov DWORD PTR [edi+2524], eax
	mov eax, DWORD PTR [edi+2400]
	mov DWORD PTR [edi+2528], eax
	mov eax, DWORD PTR [edi+2404]
	mov DWORD PTR [edi+2532], eax
	mov eax, DWORD PTR [edi+2408]
	mov DWORD PTR [edi+2536], eax
	mov eax, DWORD PTR [edi+2412]
	mov DWORD PTR [edi+2540], eax
	mov eax, DWORD PTR [edi+2416]
	mov DWORD PTR [edi+2544], eax
	mov eax, DWORD PTR [edi+2420]
	mov DWORD PTR [edi+2548], eax
	mov eax, DWORD PTR [edi+2424]
	mov DWORD PTR [edi+2552], eax
	mov eax, DWORD PTR [edi+2428]
	mov DWORD PTR [edi+2556], eax
	mov eax, DWORD PTR [edi+2432]
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2436]
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2440]
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2444]
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2448]
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2452]
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2456]
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2460]
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2464]
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2468]
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2472]
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2476]
	mov DWORD PTR [edi+2604], eax
	mov esi, 32
28:
	mov eax, 2496
	mov ecx, 2496
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 28b
	mov eax, 2496
	mov ecx, 2496
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2496]
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2500]
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2504]
	mov DWORD PTR [edi+2632], eax
	mov eax, DWORD PTR [edi+2508]
	mov DWORD PTR [edi+2636], eax
	mov eax, DWORD PTR [edi+2512]
	mov DWORD PTR [edi+2640], eax
	mov eax, DWORD PTR [edi+2516]
	mov DWORD PTR [edi+2644], eax
	mov eax, DWORD PTR [edi+2520]
	mov DWORD PTR [edi+2648], eax
	mov eax, DWORD PTR [edi+2524]
	mov DWORD PTR [edi+2652], eax
	mov eax, DWORD PTR [edi+2528]
	mov DWORD PTR [edi+2656], eax
	mov eax, DWORD PTR [edi+2532]
	mov DWORD PTR [edi+2660], eax
	mov eax, DWORD PTR [edi+2536]
	mov DWORD PTR [edi+2664], eax
	mov eax, DWORD PTR [edi+2540]
	mov DWORD PTR [edi+2668], eax
	mov eax, DWORD PTR [edi+2544]
	mov DWORD PTR [edi+2672], eax
	mov eax, DWORD PTR [edi+2548]
	mov DWORD PTR [edi+2676], eax
	mov eax, DWORD PTR [edi+2552]
	mov DWORD PTR [edi+2680], eax
	mov eax, DWORD PTR [edi+2556]
	mov DWORD PTR [edi+2684], eax
	mov eax, DWORD PTR [edi+2560]
	mov DWORD PTR [edi+2688], eax
	mov eax, DWORD PTR [edi+2564]
	mov DWORD PTR [edi+2692], eax
	mov eax, DWORD PTR [edi+2568]
	mov DWORD PTR [edi+2696], eax
	mov eax, DWORD PTR [edi+2572]
	mov DWORD PTR [edi+2700], eax
	mov eax, DWORD PTR [edi+2576]
	mov DWORD PTR [edi+2704], eax
	mov eax, DWORD PTR [edi+2580]
	mov DWORD PTR [edi+2708], eax
	mov eax, DWORD PTR [edi+2584]
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+2588]
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2592]
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2596]
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2600]
	mov DWORD PTR [edi+2728], eax
	mov eax, DWORD PTR [edi+2604]
	mov DWORD PTR [edi+2732], eax
	mov esi, 64
29:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 29b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 64
210:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 210b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 16
211:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 211b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 8
212:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 212b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 4
213:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 213b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 2
214:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 214b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2624]
	mov DWORD PTR [edi+2752], eax
	mov eax, DWORD PTR [edi+2628]
	mov DWORD PTR [edi+2756], eax
	mov eax, DWORD PTR [edi+2632]
	mov DWORD PTR [edi+2760], eax
	mov eax, DWORD PTR [edi+2636]
	mov DWORD PTR [edi+2764], eax
	mov eax, DWORD PTR [edi+2640]
	mov DWORD PTR [edi+2768], eax
	mov eax, DWORD PTR [edi+2644]
	mov DWORD PTR [edi+2772], eax
	mov eax, DWORD PTR [edi+2648]
	mov DWORD PTR [edi+2776], eax
	mov eax, DWORD PTR [edi+2652]
	mov DWORD PTR [edi+2780], eax
	mov eax, DWORD PTR [edi+2656]
	mov DWORD PTR [edi+2784], eax
	mov eax, DWORD PTR [edi+2660]
	mov DWORD PTR [edi+2788], eax
	mov eax, DWORD PTR [edi+2664]
	mov DWORD PTR [edi+2792], eax
	mov eax, DWORD PTR [edi+2668]
	mov DWORD PTR [edi+2796], eax
	mov eax, DWORD PTR [edi+2672]
	mov DWORD PTR [edi+2800], eax
	mov eax, DWORD PTR [edi+2676]
	mov DWORD PTR [edi+2804], eax
	mov eax, DWORD PTR [edi+2680]
	mov DWORD PTR [edi+2808], eax
	mov eax, DWORD PTR [edi+2684]
	mov DWORD PTR [edi+2812], eax
	mov eax, DWORD PTR [edi+2688]
	mov DWORD PTR [edi+2816], eax
	mov eax, DWORD PTR [edi+2692]
	mov DWORD PTR [edi+2820], eax
	mov eax, DWORD PTR [edi+2696]
	mov DWORD PTR [edi+2824], eax
	mov eax, DWORD PTR [edi+2700]
	mov DWORD PTR [edi+2828], eax
	mov eax, DWORD PTR [edi+2704]
	mov DWORD PTR [edi+2832], eax
	mov eax, DWORD PTR [edi+2708]
	mov DWORD PTR [edi+2836], eax
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+2840], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+2844], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+2848], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+2852], eax
	mov eax, DWORD PTR [edi+2728]
	mov DWORD PTR [edi+2856], eax
	mov eax, DWORD PTR [edi+2732]
	mov DWORD PTR [edi+2860], eax
	mov esi, 1
215:
	mov eax, 2752
	mov ecx, 2752
	mov edx, 2752
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 215b
	mov eax, 2752
	mov ecx, 2752
	mov edx, 320
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 225
216:
	mov eax, 2752
	mov ecx, 2752
	mov edx, 2752
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 216b
	mov esi, 2
217:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 217b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 320
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2752
	mov ecx, 2752
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 192
	mov edx, 2752
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 192
	mov ecx, 64
	mov edx, 2752
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3892], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3896], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3900], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3904], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3908], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3912], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3916], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3920], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3924], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3928], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3932], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3936], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3940], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3944], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3948], eax
	mov eax, DWORD PTR [edi+3840]
	add eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+3896]
	add eax, 1
	mov DWORD PTR [edi+3896], eax
	mov ebx, 0
	mov eax, DWORD PTR [edi+3840]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3840], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3844]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3844], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3848]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3848], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3852]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3852], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3856]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3856], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3860]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3860], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3864]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3864], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3868]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3868], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3872]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3872], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3876]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3876], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3880]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3880], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3884]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3884], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3888]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3888], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3892]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3892], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3896]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3896], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3900]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3900], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3904]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3904], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3908]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3908], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3912]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3912], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3916]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3916], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3920]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3920], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3924]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3924], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3928]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3928], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3932]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3932], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3936]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3936], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3940]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3940], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3944]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3944], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3948]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3948], edx
	shr ebx, 16
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+3840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+3844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+3848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+3852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+3856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+3860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+3864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+3868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+3872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+3876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+3880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+3884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+3888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+3892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+3896]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+3900]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+3904]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+3908]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+3912]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+3916]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+3920]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+3924]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+3928]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+3932]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+3936]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+3940]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+3944]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+3948]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+300], eax
	mov esi, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+192]
	and eax, 1
	ror eax, 25
	mov BYTE PTR [esi+56], al
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3892], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3896], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3900], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3904], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3908], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3912], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3916], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3920], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3924], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3928], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3932], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3936], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3940], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3944], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3948], eax
	mov eax, DWORD PTR [edi+3840]
	add eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+3896]
	add eax, 1
	mov DWORD PTR [edi+3896], eax
	mov ebx, 0
	mov eax, DWORD PTR [edi+3840]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3840], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3844]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3844], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3848]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3848], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3852]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3852], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3856]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3856], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3860]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3860], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3864]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3864], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3868]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3868], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3872]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3872], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3876]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3876], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3880]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3880], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3884]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3884], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3888]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3888], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3892]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3892], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3896]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3896], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3900]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3900], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3904]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3904], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3908]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3908], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3912]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3912], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3916]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3916], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3920]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3920], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3924]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3924], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3928]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3928], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3932]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3932], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3936]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3936], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3940]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3940], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3944]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3944], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3948]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3948], edx
	shr ebx, 16
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+3840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+3844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+3848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+3852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+3856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+3860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+3864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+3868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+3872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+3876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+3880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+3884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+3888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+3892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+3896]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+3900]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+3904]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+3908]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+3912]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+3916]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+3920]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+3924]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+3928]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+3932]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+3936]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+3940]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+3944]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+3948]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+192]
	mov BYTE PTR [esi], al
	shr eax, 8
	mov BYTE PTR [esi+1], al
	mov eax, DWORD PTR [edi+196]
	mov BYTE PTR [esi+2], al
	shr eax, 8
	mov BYTE PTR [esi+3], al
	mov eax, DWORD PTR [edi+200]
	mov BYTE PTR [esi+4], al
	shr eax, 8
	mov BYTE PTR [esi+5], al
	mov eax, DWORD PTR [edi+204]
	mov BYTE PTR [esi+6], al
	shr eax, 8
	mov BYTE PTR [esi+7], al
	mov eax, DWORD PTR [edi+208]
	mov BYTE PTR [esi+8], al
	shr eax, 8
	mov BYTE PTR [esi+9], al
	mov eax, DWORD PTR [edi+212]
	mov BYTE PTR [esi+10], al
	shr eax, 8
	mov BYTE PTR [esi+11], al
	mov eax, DWORD PTR [edi+216]
	mov BYTE PTR [esi+12], al
	shr eax, 8
	mov BYTE PTR [esi+13], al
	mov eax, DWORD PTR [edi+220]
	mov BYTE PTR [esi+14], al
	shr eax, 8
	mov BYTE PTR [esi+15], al
	mov eax, DWORD PTR [edi+224]
	mov BYTE PTR [esi+16], al
	shr eax, 8
	mov BYTE PTR [esi+17], al
	mov eax, DWORD PTR [edi+228]
	mov BYTE PTR [esi+18], al
	shr eax, 8
	mov BYTE PTR [esi+19], al
	mov eax, DWORD PTR [edi+232]
	mov BYTE PTR [esi+20], al
	shr eax, 8
	mov BYTE PTR [esi+21], al
	mov eax, DWORD PTR [edi+236]
	mov BYTE PTR [esi+22], al
	shr eax, 8
	mov BYTE PTR [esi+23], al
	mov eax, DWORD PTR [edi+240]
	mov BYTE PTR [esi+24], al
	shr eax, 8
	mov BYTE PTR [esi+25], al
	mov eax, DWORD PTR [edi+244]
	mov BYTE PTR [esi+26], al
	shr eax, 8
	mov BYTE PTR [esi+27], al
	mov eax, DWORD PTR [edi+248]
	mov BYTE PTR [esi+28], al
	shr eax, 8
	mov BYTE PTR [esi+29], al
	mov eax, DWORD PTR [edi+252]
	mov BYTE PTR [esi+30], al
	shr eax, 8
	mov BYTE PTR [esi+31], al
	mov eax, DWORD PTR [edi+256]
	mov BYTE PTR [esi+32], al
	shr eax, 8
	mov BYTE PTR [esi+33], al
	mov eax, DWORD PTR [edi+260]
	mov BYTE PTR [esi+34], al
	shr eax, 8
	mov BYTE PTR [esi+35], al
	mov eax, DWORD PTR [edi+264]
	mov BYTE PTR [esi+36], al
	shr eax, 8
	mov BYTE PTR [esi+37], al
	mov eax, DWORD PTR [edi+268]
	mov BYTE PTR [esi+38], al
	shr eax, 8
	mov BYTE PTR [esi+39], al
	mov eax, DWORD PTR [edi+272]
	mov BYTE PTR [esi+40], al
	shr eax, 8
	mov BYTE PTR [esi+41], al
	mov eax, DWORD PTR [edi+276]
	mov BYTE PTR [esi+42], al
	shr eax, 8
	mov BYTE PTR [esi+43], al
	mov eax, DWORD PTR [edi+280]
	mov BYTE PTR [esi+44], al
	shr eax, 8
	mov BYTE PTR [esi+45], al
	mov eax, DWORD PTR [edi+284]
	mov BYTE PTR [esi+46], al
	shr eax, 8
	mov BYTE PTR [esi+47], al
	mov eax, DWORD PTR [edi+288]
	mov BYTE PTR [esi+48], al
	shr eax, 8
	mov BYTE PTR [esi+49], al
	mov eax, DWORD PTR [edi+292]
	mov BYTE PTR [esi+50], al
	shr eax, 8
	mov BYTE PTR [esi+51], al
	mov eax, DWORD PTR [edi+296]
	mov BYTE PTR [esi+52], al
	shr eax, 8
	mov BYTE PTR [esi+53], al
	mov eax, DWORD PTR [edi+300]
	mov BYTE PTR [esi+54], al
	shr eax, 8
	mov BYTE PTR [esi+55], al
	mov eax, edi
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov ebp, DWORD PTR [eax+12]
	mov edi, DWORD PTR [eax+8]
	ret
	.p2align 6

vg_ed448_sign_cached:
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	mov eax, DWORD PTR [esp+288]
	mov edx, 0
	mov DWORD PTR [eax], edx
	mov DWORD PTR [eax+4], edx
	mov DWORD PTR [eax+8], edx
	mov DWORD PTR [eax+12], edx
	mov DWORD PTR [eax+16], edx
	mov DWORD PTR [eax+20], edx
	mov DWORD PTR [eax+24], edx
	mov DWORD PTR [eax+28], edx
	mov DWORD PTR [eax+32], edx
	mov DWORD PTR [eax+36], edx
	mov DWORD PTR [eax+40], edx
	mov DWORD PTR [eax+44], edx
	mov DWORD PTR [eax+48], edx
	mov DWORD PTR [eax+52], edx
	mov DWORD PTR [eax+56], edx
	mov DWORD PTR [eax+60], edx
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
	mov DWORD PTR [eax+192], edx
	mov DWORD PTR [eax+196], edx
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+264]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 57
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, 31
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+16], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_pad_scratch}
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 138
	mov DWORD PTR [esp+12], eax
	mov eax, 114
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_squeeze_scratch}
	movzx eax, BYTE PTR [esp+138]
	and eax, 252
	mov BYTE PTR [esp+138], al
	movzx eax, BYTE PTR [esp+193]
	or eax, 128
	mov BYTE PTR [esp+193], al
	mov eax, 0
	mov BYTE PTR [esp+194], al
	mov eax, DWORD PTR [esp+276]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [esp+32], eax
	mov eax, 1164405075
	mov DWORD PTR [esp+24], eax
	mov eax, 942945380
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+288]
	mov edx, 0
	mov DWORD PTR [eax], edx
	mov DWORD PTR [eax+4], edx
	mov DWORD PTR [eax+8], edx
	mov DWORD PTR [eax+12], edx
	mov DWORD PTR [eax+16], edx
	mov DWORD PTR [eax+20], edx
	mov DWORD PTR [eax+24], edx
	mov DWORD PTR [eax+28], edx
	mov DWORD PTR [eax+32], edx
	mov DWORD PTR [eax+36], edx
	mov DWORD PTR [eax+40], edx
	mov DWORD PTR [eax+44], edx
	mov DWORD PTR [eax+48], edx
	mov DWORD PTR [eax+52], edx
	mov DWORD PTR [eax+56], edx
	mov DWORD PTR [eax+60], edx
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
	mov DWORD PTR [eax+192], edx
	mov DWORD PTR [eax+196], edx
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+12], eax
	mov eax, 10
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+272]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 195
	mov DWORD PTR [esp+12], eax
	mov eax, 57
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, 31
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+16], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_pad_scratch}
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+12], eax
	mov eax, 114
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_squeeze_scratch}
	mov eax, DWORD PTR [esp+260]
	add eax, 57
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed448_scalar_reduce}
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+260]
	add eax, 57
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed448_scalar_base}
	mov eax, DWORD PTR [esp+276]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [esp+32], eax
	mov eax, 1164405075
	mov DWORD PTR [esp+24], eax
	mov eax, 942945380
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+288]
	mov edx, 0
	mov DWORD PTR [eax], edx
	mov DWORD PTR [eax+4], edx
	mov DWORD PTR [eax+8], edx
	mov DWORD PTR [eax+12], edx
	mov DWORD PTR [eax+16], edx
	mov DWORD PTR [eax+20], edx
	mov DWORD PTR [eax+24], edx
	mov DWORD PTR [eax+28], edx
	mov DWORD PTR [eax+32], edx
	mov DWORD PTR [eax+36], edx
	mov DWORD PTR [eax+40], edx
	mov DWORD PTR [eax+44], edx
	mov DWORD PTR [eax+48], edx
	mov DWORD PTR [eax+52], edx
	mov DWORD PTR [eax+56], edx
	mov DWORD PTR [eax+60], edx
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
	mov DWORD PTR [eax+192], edx
	mov DWORD PTR [eax+196], edx
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+12], eax
	mov eax, 10
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+272]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 57
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 57
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, 31
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+16], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_pad_scratch}
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+12], eax
	mov eax, 114
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_squeeze_scratch}
	mov eax, esp
	add eax, 195
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed448_scalar_reduce}
	mov eax, DWORD PTR [esp+260]
	add eax, 57
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+260]
	add eax, 57
	mov DWORD PTR [esp+4], eax
	mov eax, esp
	add eax, 195
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 138
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	call {vg_ed448_scalar_mul_add}
	mov eax, 0
	mov DWORD PTR [esp+24], eax
	mov eax, 0
	mov DWORD PTR [esp+28], eax
	mov eax, 0
	mov DWORD PTR [esp+32], eax
	mov eax, 0
	mov DWORD PTR [esp+36], eax
	mov eax, 0
	mov DWORD PTR [esp+40], eax
	mov eax, 0
	mov DWORD PTR [esp+44], eax
	mov eax, 0
	mov DWORD PTR [esp+48], eax
	mov eax, 0
	mov DWORD PTR [esp+52], eax
	mov eax, 0
	mov DWORD PTR [esp+56], eax
	mov eax, 0
	mov DWORD PTR [esp+60], eax
	mov eax, 0
	mov DWORD PTR [esp+64], eax
	mov eax, 0
	mov DWORD PTR [esp+68], eax
	mov eax, 0
	mov DWORD PTR [esp+72], eax
	mov eax, 0
	mov DWORD PTR [esp+76], eax
	mov eax, 0
	mov DWORD PTR [esp+80], eax
	mov eax, 0
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+88], eax
	mov eax, 0
	mov DWORD PTR [esp+92], eax
	mov eax, 0
	mov DWORD PTR [esp+96], eax
	mov eax, 0
	mov DWORD PTR [esp+100], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov eax, 0
	mov DWORD PTR [esp+108], eax
	mov eax, 0
	mov DWORD PTR [esp+112], eax
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov eax, 0
	mov DWORD PTR [esp+120], eax
	mov eax, 0
	mov DWORD PTR [esp+124], eax
	mov eax, 0
	mov DWORD PTR [esp+128], eax
	mov eax, 0
	mov DWORD PTR [esp+132], eax
	mov eax, 0
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+140], eax
	mov eax, 0
	mov DWORD PTR [esp+144], eax
	mov eax, 0
	mov DWORD PTR [esp+148], eax
	mov eax, 0
	mov DWORD PTR [esp+152], eax
	mov eax, 0
	mov DWORD PTR [esp+156], eax
	mov eax, 0
	mov DWORD PTR [esp+160], eax
	mov eax, 0
	mov DWORD PTR [esp+164], eax
	mov eax, 0
	mov DWORD PTR [esp+168], eax
	mov eax, 0
	mov DWORD PTR [esp+172], eax
	mov eax, 0
	mov DWORD PTR [esp+176], eax
	mov eax, 0
	mov DWORD PTR [esp+180], eax
	mov eax, 0
	mov DWORD PTR [esp+184], eax
	mov eax, 0
	mov DWORD PTR [esp+188], eax
	mov eax, 0
	mov DWORD PTR [esp+192], eax
	mov eax, 0
	mov DWORD PTR [esp+196], eax
	mov eax, 0
	mov DWORD PTR [esp+200], eax
	mov eax, 0
	mov DWORD PTR [esp+204], eax
	mov eax, 0
	mov DWORD PTR [esp+208], eax
	mov eax, 0
	mov DWORD PTR [esp+212], eax
	mov eax, 0
	mov DWORD PTR [esp+216], eax
	mov eax, 0
	mov DWORD PTR [esp+220], eax
	mov eax, 0
	mov DWORD PTR [esp+224], eax
	mov eax, 0
	mov DWORD PTR [esp+228], eax
	mov eax, 0
	mov DWORD PTR [esp+232], eax
	mov eax, 0
	mov DWORD PTR [esp+236], eax
	mov eax, 0
	mov DWORD PTR [esp+240], eax
	mov eax, 0
	mov DWORD PTR [esp+244], eax
	mov eax, 0
	mov DWORD PTR [esp+248], eax
	mov eax, 0
	mov DWORD PTR [esp+252], eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	ret
	.p2align 6

vg_ed448_verify:
	mov eax, DWORD PTR [esp+12]
	shr eax, 8
	cmp eax, 0
	je 20f
	mov eax, 0
	jmp 21f
20:
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	mov eax, DWORD PTR [esp+268]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [esp+32], eax
	mov eax, 1164405075
	mov DWORD PTR [esp+24], eax
	mov eax, 942945380
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+284]
	mov edx, 0
	mov DWORD PTR [eax], edx
	mov DWORD PTR [eax+4], edx
	mov DWORD PTR [eax+8], edx
	mov DWORD PTR [eax+12], edx
	mov DWORD PTR [eax+16], edx
	mov DWORD PTR [eax+20], edx
	mov DWORD PTR [eax+24], edx
	mov DWORD PTR [eax+28], edx
	mov DWORD PTR [eax+32], edx
	mov DWORD PTR [eax+36], edx
	mov DWORD PTR [eax+40], edx
	mov DWORD PTR [eax+44], edx
	mov DWORD PTR [eax+48], edx
	mov DWORD PTR [eax+52], edx
	mov DWORD PTR [eax+56], edx
	mov DWORD PTR [eax+60], edx
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
	mov DWORD PTR [eax+192], edx
	mov DWORD PTR [eax+196], edx
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+12], eax
	mov eax, 10
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+264]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 57
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 57
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+272]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, 31
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 208
	mov DWORD PTR [esp+16], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_pad_scratch}
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+12], eax
	mov eax, 114
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_squeeze_scratch}
	mov eax, esp
	add eax, 160
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed448_scalar_reduce}
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, esp
	add eax, 160
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	call {vg_ed448_verify_equation}
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
21:
	ret
	.p2align 6

vg_ed448_verify_equation:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+8]
	mov ebp, edi
	mov ecx, 57
20:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebp+4608], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebp+4609], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebp+4610], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebp+4611], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebp+4612], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebp+4613], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebp+4614], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebp+4615], dl
	add esi, 1
	add ebp, 8
	sub ecx, 1
	jne 20b
	mov esi, ebx
	add esi, 57
	mov ebp, edi
	mov ecx, 57
21:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebp+3072], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebp+3073], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebp+3074], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebp+3075], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebp+3076], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebp+3077], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebp+3078], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebp+3079], dl
	add esi, 1
	add ebp, 8
	sub ecx, 1
	jne 21b
	sub esi, 114
	mov eax, 0
	mov DWORD PTR [edi+16], eax
	movzx eax, BYTE PTR [esi+57]
	movzx edx, BYTE PTR [esi+58]
	ror edx, 24
	add eax, edx
	add eax, 47885
	mov DWORD PTR [edi+3840], eax
	movzx eax, BYTE PTR [esi+59]
	movzx edx, BYTE PTR [esi+60]
	ror edx, 24
	add eax, edx
	add eax, 21671
	mov DWORD PTR [edi+3844], eax
	movzx eax, BYTE PTR [esi+61]
	movzx edx, BYTE PTR [esi+62]
	ror edx, 24
	add eax, edx
	add eax, 15725
	mov DWORD PTR [edi+3848], eax
	movzx eax, BYTE PTR [esi+63]
	movzx edx, BYTE PTR [esi+64]
	ror edx, 24
	add eax, edx
	add eax, 56455
	mov DWORD PTR [edi+3852], eax
	movzx eax, BYTE PTR [esi+65]
	movzx edx, BYTE PTR [esi+66]
	ror edx, 24
	add eax, edx
	add eax, 28842
	mov DWORD PTR [edi+3856], eax
	movzx eax, BYTE PTR [esi+67]
	movzx edx, BYTE PTR [esi+68]
	ror edx, 24
	add eax, edx
	add eax, 29242
	mov DWORD PTR [edi+3860], eax
	movzx eax, BYTE PTR [esi+69]
	movzx edx, BYTE PTR [esi+70]
	ror edx, 24
	add eax, edx
	add eax, 15757
	mov DWORD PTR [edi+3864], eax
	movzx eax, BYTE PTR [esi+71]
	movzx edx, BYTE PTR [esi+72]
	ror edx, 24
	add eax, edx
	add eax, 56979
	mov DWORD PTR [edi+3868], eax
	movzx eax, BYTE PTR [esi+73]
	movzx edx, BYTE PTR [esi+74]
	ror edx, 24
	add eax, edx
	add eax, 51567
	mov DWORD PTR [edi+3872], eax
	movzx eax, BYTE PTR [esi+75]
	movzx edx, BYTE PTR [esi+76]
	ror edx, 24
	add eax, edx
	add eax, 20777
	mov DWORD PTR [edi+3876], eax
	movzx eax, BYTE PTR [esi+77]
	movzx edx, BYTE PTR [esi+78]
	ror edx, 24
	add eax, edx
	add eax, 9398
	mov DWORD PTR [edi+3880], eax
	movzx eax, BYTE PTR [esi+79]
	movzx edx, BYTE PTR [esi+80]
	ror edx, 24
	add eax, edx
	add eax, 15281
	mov DWORD PTR [edi+3884], eax
	movzx eax, BYTE PTR [esi+81]
	movzx edx, BYTE PTR [esi+82]
	ror edx, 24
	add eax, edx
	add eax, 56342
	mov DWORD PTR [edi+3888], eax
	movzx eax, BYTE PTR [esi+83]
	movzx edx, BYTE PTR [esi+84]
	ror edx, 24
	add eax, edx
	add eax, 33589
	mov DWORD PTR [edi+3892], eax
	movzx eax, BYTE PTR [esi+85]
	movzx edx, BYTE PTR [esi+86]
	ror edx, 24
	add eax, edx
	add eax, 0
	mov DWORD PTR [edi+3896], eax
	movzx eax, BYTE PTR [esi+87]
	movzx edx, BYTE PTR [esi+88]
	ror edx, 24
	add eax, edx
	add eax, 0
	mov DWORD PTR [edi+3900], eax
	movzx eax, BYTE PTR [esi+89]
	movzx edx, BYTE PTR [esi+90]
	ror edx, 24
	add eax, edx
	add eax, 0
	mov DWORD PTR [edi+3904], eax
	movzx eax, BYTE PTR [esi+91]
	movzx edx, BYTE PTR [esi+92]
	ror edx, 24
	add eax, edx
	add eax, 0
	mov DWORD PTR [edi+3908], eax
	movzx eax, BYTE PTR [esi+93]
	movzx edx, BYTE PTR [esi+94]
	ror edx, 24
	add eax, edx
	add eax, 0
	mov DWORD PTR [edi+3912], eax
	movzx eax, BYTE PTR [esi+95]
	movzx edx, BYTE PTR [esi+96]
	ror edx, 24
	add eax, edx
	add eax, 0
	mov DWORD PTR [edi+3916], eax
	movzx eax, BYTE PTR [esi+97]
	movzx edx, BYTE PTR [esi+98]
	ror edx, 24
	add eax, edx
	add eax, 0
	mov DWORD PTR [edi+3920], eax
	movzx eax, BYTE PTR [esi+99]
	movzx edx, BYTE PTR [esi+100]
	ror edx, 24
	add eax, edx
	add eax, 0
	mov DWORD PTR [edi+3924], eax
	movzx eax, BYTE PTR [esi+101]
	movzx edx, BYTE PTR [esi+102]
	ror edx, 24
	add eax, edx
	add eax, 0
	mov DWORD PTR [edi+3928], eax
	movzx eax, BYTE PTR [esi+103]
	movzx edx, BYTE PTR [esi+104]
	ror edx, 24
	add eax, edx
	add eax, 0
	mov DWORD PTR [edi+3932], eax
	movzx eax, BYTE PTR [esi+105]
	movzx edx, BYTE PTR [esi+106]
	ror edx, 24
	add eax, edx
	add eax, 0
	mov DWORD PTR [edi+3936], eax
	movzx eax, BYTE PTR [esi+107]
	movzx edx, BYTE PTR [esi+108]
	ror edx, 24
	add eax, edx
	add eax, 0
	mov DWORD PTR [edi+3940], eax
	movzx eax, BYTE PTR [esi+109]
	movzx edx, BYTE PTR [esi+110]
	ror edx, 24
	add eax, edx
	add eax, 0
	mov DWORD PTR [edi+3944], eax
	movzx eax, BYTE PTR [esi+111]
	movzx edx, BYTE PTR [esi+112]
	ror edx, 24
	add eax, edx
	add eax, 49152
	mov DWORD PTR [edi+3948], eax
	mov ebx, 0
	mov eax, DWORD PTR [edi+3840]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3840], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3844]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3844], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3848]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3848], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3852]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3852], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3856]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3856], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3860]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3860], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3864]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3864], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3868]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3868], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3872]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3872], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3876]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3876], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3880]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3880], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3884]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3884], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3888]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3888], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3892]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3892], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3896]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3896], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3900]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3900], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3904]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3904], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3908]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3908], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3912]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3912], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3916]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3916], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3920]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3920], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3924]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3924], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3928]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3928], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3932]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3932], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3936]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3936], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3940]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3940], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3944]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3944], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3948]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3948], edx
	shr ebx, 16
	movzx eax, BYTE PTR [esi+113]
	or eax, ebx
	or eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+16], eax
	mov ebp, edi
	add ebp, 64
	mov ebx, 0
	mov eax, 704
22:
	mov DWORD PTR [ebp], ebx
	add ebp, 4
	sub eax, 1
	jne 22b
	mov ebp, edi
	add ebp, 64
	mov eax, 1
	mov DWORD PTR [ebp+128], eax
	mov eax, 1
	mov DWORD PTR [ebp+256], eax
	mov eax, 49246
	mov DWORD PTR [ebp+1024], eax
	mov eax, 50956
	mov DWORD PTR [ebp+1028], eax
	mov eax, 43051
	mov DWORD PTR [ebp+1032], eax
	mov eax, 9766
	mov DWORD PTR [ebp+1036], eax
	mov eax, 37774
	mov DWORD PTR [ebp+1040], eax
	mov eax, 35584
	mov DWORD PTR [ebp+1044], eax
	mov eax, 32993
	mov DWORD PTR [ebp+1048], eax
	mov eax, 17211
	mov DWORD PTR [ebp+1052], eax
	mov eax, 25873
	mov DWORD PTR [ebp+1056], eax
	mov eax, 10934
	mov DWORD PTR [ebp+1060], eax
	mov eax, 6903
	mov DWORD PTR [ebp+1064], eax
	mov eax, 4782
	mov DWORD PTR [ebp+1068], eax
	mov eax, 42084
	mov DWORD PTR [ebp+1072], eax
	mov eax, 41939
	mov DWORD PTR [ebp+1076], eax
	mov eax, 58148
	mov DWORD PTR [ebp+1080], eax
	mov eax, 60013
	mov DWORD PTR [ebp+1084], eax
	mov eax, 5991
	mov DWORD PTR [ebp+1088], eax
	mov eax, 18191
	mov DWORD PTR [ebp+1092], eax
	mov eax, 25968
	mov DWORD PTR [ebp+1096], eax
	mov eax, 40468
	mov DWORD PTR [ebp+1100], eax
	mov eax, 14042
	mov DWORD PTR [ebp+1104], eax
	mov eax, 8895
	mov DWORD PTR [ebp+1108], eax
	mov eax, 5542
	mov DWORD PTR [ebp+1112], eax
	mov eax, 8733
	mov DWORD PTR [ebp+1116], eax
	mov eax, 3565
	mov DWORD PTR [ebp+1120], eax
	mov eax, 27629
	mov DWORD PTR [ebp+1124], eax
	mov eax, 28870
	mov DWORD PTR [ebp+1128], eax
	mov eax, 20249
	mov DWORD PTR [ebp+1132], eax
	mov eax, 64020
	mov DWORD PTR [ebp+1152], eax
	mov eax, 62000
	mov DWORD PTR [ebp+1156], eax
	mov eax, 31067
	mov DWORD PTR [ebp+1160], eax
	mov eax, 38920
	mov DWORD PTR [ebp+1164], eax
	mov eax, 51373
	mov DWORD PTR [ebp+1168], eax
	mov eax, 20183
	mov DWORD PTR [ebp+1172], eax
	mov eax, 4908
	mov DWORD PTR [ebp+1176], eax
	mov eax, 64957
	mov DWORD PTR [ebp+1180], eax
	mov eax, 14788
	mov DWORD PTR [ebp+1184], eax
	mov eax, 59004
	mov DWORD PTR [ebp+1188], eax
	mov eax, 65308
	mov DWORD PTR [ebp+1192], eax
	mov eax, 15059
	mov DWORD PTR [ebp+1196], eax
	mov eax, 49879
	mov DWORD PTR [ebp+1200], eax
	mov eax, 1440
	mov DWORD PTR [ebp+1204], eax
	mov eax, 39966
	mov DWORD PTR [ebp+1208], eax
	mov eax, 34680
	mov DWORD PTR [ebp+1212], eax
	mov eax, 38976
	mov DWORD PTR [ebp+1216], eax
	mov eax, 27811
	mov DWORD PTR [ebp+1220], eax
	mov eax, 29555
	mov DWORD PTR [ebp+1224], eax
	mov eax, 19434
	mov DWORD PTR [ebp+1228], eax
	mov eax, 51042
	mov DWORD PTR [ebp+1232], eax
	mov eax, 22217
	mov DWORD PTR [ebp+1236], eax
	mov eax, 8247
	mov DWORD PTR [ebp+1240], eax
	mov eax, 34934
	mov DWORD PTR [ebp+1244], eax
	mov eax, 48164
	mov DWORD PTR [ebp+1248], eax
	mov eax, 28342
	mov DWORD PTR [ebp+1252], eax
	mov eax, 18033
	mov DWORD PTR [ebp+1256], eax
	mov eax, 26943
	mov DWORD PTR [ebp+1260], eax
	mov eax, 1
	mov DWORD PTR [ebp+1280], eax
	mov eax, 26454
	mov DWORD PTR [ebp+1408], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1412], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1416], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1420], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1424], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1428], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1432], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1436], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1440], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1444], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1448], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1452], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1456], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1460], eax
	mov eax, 65534
	mov DWORD PTR [ebp+1464], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1468], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1472], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1476], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1480], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1484], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1488], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1492], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1496], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1500], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1504], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1508], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1512], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1516], eax
	mov esi, DWORD PTR [esp+8]
	mov DWORD PTR [edi+4352], esi
	mov ebx, 2
	mov DWORD PTR [edi+4356], ebx
23:
	mov eax, DWORD PTR [edi+832]
	mov DWORD PTR [edi+4096], eax
	mov eax, DWORD PTR [edi+836]
	mov DWORD PTR [edi+4100], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+4104], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+4108], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+4112], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+4116], eax
	mov eax, DWORD PTR [edi+856]
	mov DWORD PTR [edi+4120], eax
	mov eax, DWORD PTR [edi+860]
	mov DWORD PTR [edi+4124], eax
	mov eax, DWORD PTR [edi+864]
	mov DWORD PTR [edi+4128], eax
	mov eax, DWORD PTR [edi+868]
	mov DWORD PTR [edi+4132], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+4136], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+4140], eax
	mov eax, DWORD PTR [edi+880]
	mov DWORD PTR [edi+4144], eax
	mov eax, DWORD PTR [edi+884]
	mov DWORD PTR [edi+4148], eax
	mov eax, DWORD PTR [edi+888]
	mov DWORD PTR [edi+4152], eax
	mov eax, DWORD PTR [edi+892]
	mov DWORD PTR [edi+4156], eax
	mov eax, DWORD PTR [edi+896]
	mov DWORD PTR [edi+4160], eax
	mov eax, DWORD PTR [edi+900]
	mov DWORD PTR [edi+4164], eax
	mov eax, DWORD PTR [edi+904]
	mov DWORD PTR [edi+4168], eax
	mov eax, DWORD PTR [edi+908]
	mov DWORD PTR [edi+4172], eax
	mov eax, DWORD PTR [edi+912]
	mov DWORD PTR [edi+4176], eax
	mov eax, DWORD PTR [edi+916]
	mov DWORD PTR [edi+4180], eax
	mov eax, DWORD PTR [edi+920]
	mov DWORD PTR [edi+4184], eax
	mov eax, DWORD PTR [edi+924]
	mov DWORD PTR [edi+4188], eax
	mov eax, DWORD PTR [edi+928]
	mov DWORD PTR [edi+4192], eax
	mov eax, DWORD PTR [edi+932]
	mov DWORD PTR [edi+4196], eax
	mov eax, DWORD PTR [edi+936]
	mov DWORD PTR [edi+4200], eax
	mov eax, DWORD PTR [edi+940]
	mov DWORD PTR [edi+4204], eax
	mov eax, DWORD PTR [edi+960]
	mov DWORD PTR [edi+4224], eax
	mov eax, DWORD PTR [edi+964]
	mov DWORD PTR [edi+4228], eax
	mov eax, DWORD PTR [edi+968]
	mov DWORD PTR [edi+4232], eax
	mov eax, DWORD PTR [edi+972]
	mov DWORD PTR [edi+4236], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [edi+4240], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [edi+4244], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [edi+4248], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [edi+4252], eax
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [edi+4256], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [edi+4260], eax
	mov eax, DWORD PTR [edi+1000]
	mov DWORD PTR [edi+4264], eax
	mov eax, DWORD PTR [edi+1004]
	mov DWORD PTR [edi+4268], eax
	mov eax, DWORD PTR [edi+1008]
	mov DWORD PTR [edi+4272], eax
	mov eax, DWORD PTR [edi+1012]
	mov DWORD PTR [edi+4276], eax
	mov eax, DWORD PTR [edi+1016]
	mov DWORD PTR [edi+4280], eax
	mov eax, DWORD PTR [edi+1020]
	mov DWORD PTR [edi+4284], eax
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [edi+4288], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [edi+4292], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [edi+4296], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [edi+4300], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [edi+4304], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [edi+4308], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [edi+4312], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [edi+4316], eax
	mov eax, DWORD PTR [edi+1056]
	mov DWORD PTR [edi+4320], eax
	mov eax, DWORD PTR [edi+1060]
	mov DWORD PTR [edi+4324], eax
	mov eax, DWORD PTR [edi+1064]
	mov DWORD PTR [edi+4328], eax
	mov eax, DWORD PTR [edi+1068]
	mov DWORD PTR [edi+4332], eax
	mov esi, DWORD PTR [edi+4352]
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [esi+1]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+960], eax
	movzx eax, BYTE PTR [esi+2]
	movzx edx, BYTE PTR [esi+3]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+964], eax
	movzx eax, BYTE PTR [esi+4]
	movzx edx, BYTE PTR [esi+5]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+968], eax
	movzx eax, BYTE PTR [esi+6]
	movzx edx, BYTE PTR [esi+7]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+972], eax
	movzx eax, BYTE PTR [esi+8]
	movzx edx, BYTE PTR [esi+9]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+976], eax
	movzx eax, BYTE PTR [esi+10]
	movzx edx, BYTE PTR [esi+11]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+980], eax
	movzx eax, BYTE PTR [esi+12]
	movzx edx, BYTE PTR [esi+13]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+984], eax
	movzx eax, BYTE PTR [esi+14]
	movzx edx, BYTE PTR [esi+15]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+988], eax
	movzx eax, BYTE PTR [esi+16]
	movzx edx, BYTE PTR [esi+17]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+992], eax
	movzx eax, BYTE PTR [esi+18]
	movzx edx, BYTE PTR [esi+19]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+996], eax
	movzx eax, BYTE PTR [esi+20]
	movzx edx, BYTE PTR [esi+21]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1000], eax
	movzx eax, BYTE PTR [esi+22]
	movzx edx, BYTE PTR [esi+23]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1004], eax
	movzx eax, BYTE PTR [esi+24]
	movzx edx, BYTE PTR [esi+25]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1008], eax
	movzx eax, BYTE PTR [esi+26]
	movzx edx, BYTE PTR [esi+27]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1012], eax
	movzx eax, BYTE PTR [esi+28]
	movzx edx, BYTE PTR [esi+29]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1016], eax
	movzx eax, BYTE PTR [esi+30]
	movzx edx, BYTE PTR [esi+31]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1020], eax
	movzx eax, BYTE PTR [esi+32]
	movzx edx, BYTE PTR [esi+33]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1024], eax
	movzx eax, BYTE PTR [esi+34]
	movzx edx, BYTE PTR [esi+35]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1028], eax
	movzx eax, BYTE PTR [esi+36]
	movzx edx, BYTE PTR [esi+37]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1032], eax
	movzx eax, BYTE PTR [esi+38]
	movzx edx, BYTE PTR [esi+39]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1036], eax
	movzx eax, BYTE PTR [esi+40]
	movzx edx, BYTE PTR [esi+41]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1040], eax
	movzx eax, BYTE PTR [esi+42]
	movzx edx, BYTE PTR [esi+43]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1044], eax
	movzx eax, BYTE PTR [esi+44]
	movzx edx, BYTE PTR [esi+45]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1048], eax
	movzx eax, BYTE PTR [esi+46]
	movzx edx, BYTE PTR [esi+47]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1052], eax
	movzx eax, BYTE PTR [esi+48]
	movzx edx, BYTE PTR [esi+49]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1056], eax
	movzx eax, BYTE PTR [esi+50]
	movzx edx, BYTE PTR [esi+51]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1060], eax
	movzx eax, BYTE PTR [esi+52]
	movzx edx, BYTE PTR [esi+53]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1064], eax
	movzx eax, BYTE PTR [esi+54]
	movzx edx, BYTE PTR [esi+55]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+1068], eax
	movzx eax, BYTE PTR [esi+56]
	mov edx, eax
	shr edx, 7
	mov DWORD PTR [edi+20], edx
	and eax, 127
	or eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+960]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+964]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+968]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+972]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+1000]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+1004]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+1008]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+1012]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+1016]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+1020]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+1056]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+1060]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+1064]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+1068]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3892], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3896], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3900], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3904], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3908], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3912], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3916], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3920], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3924], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3928], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3932], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3936], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3940], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3944], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3948], eax
	mov eax, DWORD PTR [edi+3840]
	add eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+3896]
	add eax, 1
	mov DWORD PTR [edi+3896], eax
	mov ebx, 0
	mov eax, DWORD PTR [edi+3840]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3840], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3844]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3844], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3848]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3848], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3852]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3852], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3856]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3856], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3860]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3860], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3864]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3864], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3868]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3868], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3872]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3872], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3876]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3876], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3880]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3880], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3884]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3884], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3888]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3888], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3892]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3892], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3896]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3896], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3900]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3900], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3904]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3904], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3908]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3908], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3912]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3912], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3916]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3916], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3920]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3920], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3924]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3924], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3928]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3928], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3932]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3932], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3936]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3936], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3940]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3940], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3944]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3944], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3948]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3948], edx
	shr ebx, 16
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+3840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+3844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+3848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+3852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+3856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+3860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+3864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+3868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+3872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+3876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+3880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+3884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+3888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+3892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+3896]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+3900]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+3904]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+3908]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+3912]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+3916]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+3920]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+3924]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+3928]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+3932]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+3936]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+3940]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+3944]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+3948]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+300], eax
	mov ecx, 0
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [edi+960]
	or ecx, eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [edi+964]
	or ecx, eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [edi+968]
	or ecx, eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [edi+972]
	or ecx, eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [edi+976]
	or ecx, eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [edi+980]
	or ecx, eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [edi+984]
	or ecx, eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [edi+988]
	or ecx, eax
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [edi+992]
	or ecx, eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [edi+996]
	or ecx, eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [edi+1000]
	or ecx, eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [edi+1004]
	or ecx, eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [edi+1008]
	or ecx, eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [edi+1012]
	or ecx, eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [edi+1016]
	or ecx, eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [edi+1020]
	or ecx, eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [edi+1024]
	or ecx, eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [edi+1028]
	or ecx, eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [edi+1032]
	or ecx, eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [edi+1036]
	or ecx, eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [edi+1040]
	or ecx, eax
	mov eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [edi+1044]
	or ecx, eax
	mov eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [edi+1048]
	or ecx, eax
	mov eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [edi+1052]
	or ecx, eax
	mov eax, DWORD PTR [edi+288]
	xor eax, DWORD PTR [edi+1056]
	or ecx, eax
	mov eax, DWORD PTR [edi+292]
	xor eax, DWORD PTR [edi+1060]
	or ecx, eax
	mov eax, DWORD PTR [edi+296]
	xor eax, DWORD PTR [edi+1064]
	or ecx, eax
	mov eax, DWORD PTR [edi+300]
	xor eax, DWORD PTR [edi+1068]
	or ecx, eax
	or ecx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+16], ecx
	mov eax, 1600
	mov ecx, 960
	mov edx, 960
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1600
	mov edx, 1344
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 1472
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 448
	mov edx, 1344
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 1728
	mov edx, 448
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 576
	mov edx, 576
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 1728
	mov edx, 1728
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 704
	mov edx, 1728
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 704
	mov edx, 448
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 832
	mov edx, 576
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1600]
	mov DWORD PTR [edi+1856], eax
	mov eax, DWORD PTR [edi+1604]
	mov DWORD PTR [edi+1860], eax
	mov eax, DWORD PTR [edi+1608]
	mov DWORD PTR [edi+1864], eax
	mov eax, DWORD PTR [edi+1612]
	mov DWORD PTR [edi+1868], eax
	mov eax, DWORD PTR [edi+1616]
	mov DWORD PTR [edi+1872], eax
	mov eax, DWORD PTR [edi+1620]
	mov DWORD PTR [edi+1876], eax
	mov eax, DWORD PTR [edi+1624]
	mov DWORD PTR [edi+1880], eax
	mov eax, DWORD PTR [edi+1628]
	mov DWORD PTR [edi+1884], eax
	mov eax, DWORD PTR [edi+1632]
	mov DWORD PTR [edi+1888], eax
	mov eax, DWORD PTR [edi+1636]
	mov DWORD PTR [edi+1892], eax
	mov eax, DWORD PTR [edi+1640]
	mov DWORD PTR [edi+1896], eax
	mov eax, DWORD PTR [edi+1644]
	mov DWORD PTR [edi+1900], eax
	mov eax, DWORD PTR [edi+1648]
	mov DWORD PTR [edi+1904], eax
	mov eax, DWORD PTR [edi+1652]
	mov DWORD PTR [edi+1908], eax
	mov eax, DWORD PTR [edi+1656]
	mov DWORD PTR [edi+1912], eax
	mov eax, DWORD PTR [edi+1660]
	mov DWORD PTR [edi+1916], eax
	mov eax, DWORD PTR [edi+1664]
	mov DWORD PTR [edi+1920], eax
	mov eax, DWORD PTR [edi+1668]
	mov DWORD PTR [edi+1924], eax
	mov eax, DWORD PTR [edi+1672]
	mov DWORD PTR [edi+1928], eax
	mov eax, DWORD PTR [edi+1676]
	mov DWORD PTR [edi+1932], eax
	mov eax, DWORD PTR [edi+1680]
	mov DWORD PTR [edi+1936], eax
	mov eax, DWORD PTR [edi+1684]
	mov DWORD PTR [edi+1940], eax
	mov eax, DWORD PTR [edi+1688]
	mov DWORD PTR [edi+1944], eax
	mov eax, DWORD PTR [edi+1692]
	mov DWORD PTR [edi+1948], eax
	mov eax, DWORD PTR [edi+1696]
	mov DWORD PTR [edi+1952], eax
	mov eax, DWORD PTR [edi+1700]
	mov DWORD PTR [edi+1956], eax
	mov eax, DWORD PTR [edi+1704]
	mov DWORD PTR [edi+1960], eax
	mov eax, DWORD PTR [edi+1708]
	mov DWORD PTR [edi+1964], eax
	mov esi, 1
24:
	mov eax, 1856
	mov ecx, 1856
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 24b
	mov eax, 1856
	mov ecx, 1856
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1856]
	mov DWORD PTR [edi+1984], eax
	mov eax, DWORD PTR [edi+1860]
	mov DWORD PTR [edi+1988], eax
	mov eax, DWORD PTR [edi+1864]
	mov DWORD PTR [edi+1992], eax
	mov eax, DWORD PTR [edi+1868]
	mov DWORD PTR [edi+1996], eax
	mov eax, DWORD PTR [edi+1872]
	mov DWORD PTR [edi+2000], eax
	mov eax, DWORD PTR [edi+1876]
	mov DWORD PTR [edi+2004], eax
	mov eax, DWORD PTR [edi+1880]
	mov DWORD PTR [edi+2008], eax
	mov eax, DWORD PTR [edi+1884]
	mov DWORD PTR [edi+2012], eax
	mov eax, DWORD PTR [edi+1888]
	mov DWORD PTR [edi+2016], eax
	mov eax, DWORD PTR [edi+1892]
	mov DWORD PTR [edi+2020], eax
	mov eax, DWORD PTR [edi+1896]
	mov DWORD PTR [edi+2024], eax
	mov eax, DWORD PTR [edi+1900]
	mov DWORD PTR [edi+2028], eax
	mov eax, DWORD PTR [edi+1904]
	mov DWORD PTR [edi+2032], eax
	mov eax, DWORD PTR [edi+1908]
	mov DWORD PTR [edi+2036], eax
	mov eax, DWORD PTR [edi+1912]
	mov DWORD PTR [edi+2040], eax
	mov eax, DWORD PTR [edi+1916]
	mov DWORD PTR [edi+2044], eax
	mov eax, DWORD PTR [edi+1920]
	mov DWORD PTR [edi+2048], eax
	mov eax, DWORD PTR [edi+1924]
	mov DWORD PTR [edi+2052], eax
	mov eax, DWORD PTR [edi+1928]
	mov DWORD PTR [edi+2056], eax
	mov eax, DWORD PTR [edi+1932]
	mov DWORD PTR [edi+2060], eax
	mov eax, DWORD PTR [edi+1936]
	mov DWORD PTR [edi+2064], eax
	mov eax, DWORD PTR [edi+1940]
	mov DWORD PTR [edi+2068], eax
	mov eax, DWORD PTR [edi+1944]
	mov DWORD PTR [edi+2072], eax
	mov eax, DWORD PTR [edi+1948]
	mov DWORD PTR [edi+2076], eax
	mov eax, DWORD PTR [edi+1952]
	mov DWORD PTR [edi+2080], eax
	mov eax, DWORD PTR [edi+1956]
	mov DWORD PTR [edi+2084], eax
	mov eax, DWORD PTR [edi+1960]
	mov DWORD PTR [edi+2088], eax
	mov eax, DWORD PTR [edi+1964]
	mov DWORD PTR [edi+2092], eax
	mov esi, 2
25:
	mov eax, 1984
	mov ecx, 1984
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 25b
	mov eax, 1984
	mov ecx, 1984
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1984]
	mov DWORD PTR [edi+2112], eax
	mov eax, DWORD PTR [edi+1988]
	mov DWORD PTR [edi+2116], eax
	mov eax, DWORD PTR [edi+1992]
	mov DWORD PTR [edi+2120], eax
	mov eax, DWORD PTR [edi+1996]
	mov DWORD PTR [edi+2124], eax
	mov eax, DWORD PTR [edi+2000]
	mov DWORD PTR [edi+2128], eax
	mov eax, DWORD PTR [edi+2004]
	mov DWORD PTR [edi+2132], eax
	mov eax, DWORD PTR [edi+2008]
	mov DWORD PTR [edi+2136], eax
	mov eax, DWORD PTR [edi+2012]
	mov DWORD PTR [edi+2140], eax
	mov eax, DWORD PTR [edi+2016]
	mov DWORD PTR [edi+2144], eax
	mov eax, DWORD PTR [edi+2020]
	mov DWORD PTR [edi+2148], eax
	mov eax, DWORD PTR [edi+2024]
	mov DWORD PTR [edi+2152], eax
	mov eax, DWORD PTR [edi+2028]
	mov DWORD PTR [edi+2156], eax
	mov eax, DWORD PTR [edi+2032]
	mov DWORD PTR [edi+2160], eax
	mov eax, DWORD PTR [edi+2036]
	mov DWORD PTR [edi+2164], eax
	mov eax, DWORD PTR [edi+2040]
	mov DWORD PTR [edi+2168], eax
	mov eax, DWORD PTR [edi+2044]
	mov DWORD PTR [edi+2172], eax
	mov eax, DWORD PTR [edi+2048]
	mov DWORD PTR [edi+2176], eax
	mov eax, DWORD PTR [edi+2052]
	mov DWORD PTR [edi+2180], eax
	mov eax, DWORD PTR [edi+2056]
	mov DWORD PTR [edi+2184], eax
	mov eax, DWORD PTR [edi+2060]
	mov DWORD PTR [edi+2188], eax
	mov eax, DWORD PTR [edi+2064]
	mov DWORD PTR [edi+2192], eax
	mov eax, DWORD PTR [edi+2068]
	mov DWORD PTR [edi+2196], eax
	mov eax, DWORD PTR [edi+2072]
	mov DWORD PTR [edi+2200], eax
	mov eax, DWORD PTR [edi+2076]
	mov DWORD PTR [edi+2204], eax
	mov eax, DWORD PTR [edi+2080]
	mov DWORD PTR [edi+2208], eax
	mov eax, DWORD PTR [edi+2084]
	mov DWORD PTR [edi+2212], eax
	mov eax, DWORD PTR [edi+2088]
	mov DWORD PTR [edi+2216], eax
	mov eax, DWORD PTR [edi+2092]
	mov DWORD PTR [edi+2220], eax
	mov esi, 4
26:
	mov eax, 2112
	mov ecx, 2112
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 26b
	mov eax, 2112
	mov ecx, 2112
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2112]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2116]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2120]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2124]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2128]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2132]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2136]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2140]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2144]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2148]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2300], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2304], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2308], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2312], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2316], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2320], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2324], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2328], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2332], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2336], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2340], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2344], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2348], eax
	mov esi, 8
27:
	mov eax, 2240
	mov ecx, 2240
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 27b
	mov eax, 2240
	mov ecx, 2240
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2240]
	mov DWORD PTR [edi+2368], eax
	mov eax, DWORD PTR [edi+2244]
	mov DWORD PTR [edi+2372], eax
	mov eax, DWORD PTR [edi+2248]
	mov DWORD PTR [edi+2376], eax
	mov eax, DWORD PTR [edi+2252]
	mov DWORD PTR [edi+2380], eax
	mov eax, DWORD PTR [edi+2256]
	mov DWORD PTR [edi+2384], eax
	mov eax, DWORD PTR [edi+2260]
	mov DWORD PTR [edi+2388], eax
	mov eax, DWORD PTR [edi+2264]
	mov DWORD PTR [edi+2392], eax
	mov eax, DWORD PTR [edi+2268]
	mov DWORD PTR [edi+2396], eax
	mov eax, DWORD PTR [edi+2272]
	mov DWORD PTR [edi+2400], eax
	mov eax, DWORD PTR [edi+2276]
	mov DWORD PTR [edi+2404], eax
	mov eax, DWORD PTR [edi+2280]
	mov DWORD PTR [edi+2408], eax
	mov eax, DWORD PTR [edi+2284]
	mov DWORD PTR [edi+2412], eax
	mov eax, DWORD PTR [edi+2288]
	mov DWORD PTR [edi+2416], eax
	mov eax, DWORD PTR [edi+2292]
	mov DWORD PTR [edi+2420], eax
	mov eax, DWORD PTR [edi+2296]
	mov DWORD PTR [edi+2424], eax
	mov eax, DWORD PTR [edi+2300]
	mov DWORD PTR [edi+2428], eax
	mov eax, DWORD PTR [edi+2304]
	mov DWORD PTR [edi+2432], eax
	mov eax, DWORD PTR [edi+2308]
	mov DWORD PTR [edi+2436], eax
	mov eax, DWORD PTR [edi+2312]
	mov DWORD PTR [edi+2440], eax
	mov eax, DWORD PTR [edi+2316]
	mov DWORD PTR [edi+2444], eax
	mov eax, DWORD PTR [edi+2320]
	mov DWORD PTR [edi+2448], eax
	mov eax, DWORD PTR [edi+2324]
	mov DWORD PTR [edi+2452], eax
	mov eax, DWORD PTR [edi+2328]
	mov DWORD PTR [edi+2456], eax
	mov eax, DWORD PTR [edi+2332]
	mov DWORD PTR [edi+2460], eax
	mov eax, DWORD PTR [edi+2336]
	mov DWORD PTR [edi+2464], eax
	mov eax, DWORD PTR [edi+2340]
	mov DWORD PTR [edi+2468], eax
	mov eax, DWORD PTR [edi+2344]
	mov DWORD PTR [edi+2472], eax
	mov eax, DWORD PTR [edi+2348]
	mov DWORD PTR [edi+2476], eax
	mov esi, 16
28:
	mov eax, 2368
	mov ecx, 2368
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 28b
	mov eax, 2368
	mov ecx, 2368
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2368]
	mov DWORD PTR [edi+2496], eax
	mov eax, DWORD PTR [edi+2372]
	mov DWORD PTR [edi+2500], eax
	mov eax, DWORD PTR [edi+2376]
	mov DWORD PTR [edi+2504], eax
	mov eax, DWORD PTR [edi+2380]
	mov DWORD PTR [edi+2508], eax
	mov eax, DWORD PTR [edi+2384]
	mov DWORD PTR [edi+2512], eax
	mov eax, DWORD PTR [edi+2388]
	mov DWORD PTR [edi+2516], eax
	mov eax, DWORD PTR [edi+2392]
	mov DWORD PTR [edi+2520], eax
	mov eax, DWORD PTR [edi+2396]
	mov DWORD PTR [edi+2524], eax
	mov eax, DWORD PTR [edi+2400]
	mov DWORD PTR [edi+2528], eax
	mov eax, DWORD PTR [edi+2404]
	mov DWORD PTR [edi+2532], eax
	mov eax, DWORD PTR [edi+2408]
	mov DWORD PTR [edi+2536], eax
	mov eax, DWORD PTR [edi+2412]
	mov DWORD PTR [edi+2540], eax
	mov eax, DWORD PTR [edi+2416]
	mov DWORD PTR [edi+2544], eax
	mov eax, DWORD PTR [edi+2420]
	mov DWORD PTR [edi+2548], eax
	mov eax, DWORD PTR [edi+2424]
	mov DWORD PTR [edi+2552], eax
	mov eax, DWORD PTR [edi+2428]
	mov DWORD PTR [edi+2556], eax
	mov eax, DWORD PTR [edi+2432]
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2436]
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2440]
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2444]
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2448]
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2452]
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2456]
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2460]
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2464]
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2468]
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2472]
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2476]
	mov DWORD PTR [edi+2604], eax
	mov esi, 32
29:
	mov eax, 2496
	mov ecx, 2496
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 29b
	mov eax, 2496
	mov ecx, 2496
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2496]
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2500]
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2504]
	mov DWORD PTR [edi+2632], eax
	mov eax, DWORD PTR [edi+2508]
	mov DWORD PTR [edi+2636], eax
	mov eax, DWORD PTR [edi+2512]
	mov DWORD PTR [edi+2640], eax
	mov eax, DWORD PTR [edi+2516]
	mov DWORD PTR [edi+2644], eax
	mov eax, DWORD PTR [edi+2520]
	mov DWORD PTR [edi+2648], eax
	mov eax, DWORD PTR [edi+2524]
	mov DWORD PTR [edi+2652], eax
	mov eax, DWORD PTR [edi+2528]
	mov DWORD PTR [edi+2656], eax
	mov eax, DWORD PTR [edi+2532]
	mov DWORD PTR [edi+2660], eax
	mov eax, DWORD PTR [edi+2536]
	mov DWORD PTR [edi+2664], eax
	mov eax, DWORD PTR [edi+2540]
	mov DWORD PTR [edi+2668], eax
	mov eax, DWORD PTR [edi+2544]
	mov DWORD PTR [edi+2672], eax
	mov eax, DWORD PTR [edi+2548]
	mov DWORD PTR [edi+2676], eax
	mov eax, DWORD PTR [edi+2552]
	mov DWORD PTR [edi+2680], eax
	mov eax, DWORD PTR [edi+2556]
	mov DWORD PTR [edi+2684], eax
	mov eax, DWORD PTR [edi+2560]
	mov DWORD PTR [edi+2688], eax
	mov eax, DWORD PTR [edi+2564]
	mov DWORD PTR [edi+2692], eax
	mov eax, DWORD PTR [edi+2568]
	mov DWORD PTR [edi+2696], eax
	mov eax, DWORD PTR [edi+2572]
	mov DWORD PTR [edi+2700], eax
	mov eax, DWORD PTR [edi+2576]
	mov DWORD PTR [edi+2704], eax
	mov eax, DWORD PTR [edi+2580]
	mov DWORD PTR [edi+2708], eax
	mov eax, DWORD PTR [edi+2584]
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+2588]
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2592]
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2596]
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2600]
	mov DWORD PTR [edi+2728], eax
	mov eax, DWORD PTR [edi+2604]
	mov DWORD PTR [edi+2732], eax
	mov esi, 64
210:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 210b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 64
211:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 211b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 16
212:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 212b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 8
213:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 213b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 4
214:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 214b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 2
215:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 215b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2624]
	mov DWORD PTR [edi+2752], eax
	mov eax, DWORD PTR [edi+2628]
	mov DWORD PTR [edi+2756], eax
	mov eax, DWORD PTR [edi+2632]
	mov DWORD PTR [edi+2760], eax
	mov eax, DWORD PTR [edi+2636]
	mov DWORD PTR [edi+2764], eax
	mov eax, DWORD PTR [edi+2640]
	mov DWORD PTR [edi+2768], eax
	mov eax, DWORD PTR [edi+2644]
	mov DWORD PTR [edi+2772], eax
	mov eax, DWORD PTR [edi+2648]
	mov DWORD PTR [edi+2776], eax
	mov eax, DWORD PTR [edi+2652]
	mov DWORD PTR [edi+2780], eax
	mov eax, DWORD PTR [edi+2656]
	mov DWORD PTR [edi+2784], eax
	mov eax, DWORD PTR [edi+2660]
	mov DWORD PTR [edi+2788], eax
	mov eax, DWORD PTR [edi+2664]
	mov DWORD PTR [edi+2792], eax
	mov eax, DWORD PTR [edi+2668]
	mov DWORD PTR [edi+2796], eax
	mov eax, DWORD PTR [edi+2672]
	mov DWORD PTR [edi+2800], eax
	mov eax, DWORD PTR [edi+2676]
	mov DWORD PTR [edi+2804], eax
	mov eax, DWORD PTR [edi+2680]
	mov DWORD PTR [edi+2808], eax
	mov eax, DWORD PTR [edi+2684]
	mov DWORD PTR [edi+2812], eax
	mov eax, DWORD PTR [edi+2688]
	mov DWORD PTR [edi+2816], eax
	mov eax, DWORD PTR [edi+2692]
	mov DWORD PTR [edi+2820], eax
	mov eax, DWORD PTR [edi+2696]
	mov DWORD PTR [edi+2824], eax
	mov eax, DWORD PTR [edi+2700]
	mov DWORD PTR [edi+2828], eax
	mov eax, DWORD PTR [edi+2704]
	mov DWORD PTR [edi+2832], eax
	mov eax, DWORD PTR [edi+2708]
	mov DWORD PTR [edi+2836], eax
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+2840], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+2844], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+2848], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+2852], eax
	mov eax, DWORD PTR [edi+2728]
	mov DWORD PTR [edi+2856], eax
	mov eax, DWORD PTR [edi+2732]
	mov DWORD PTR [edi+2860], eax
	mov esi, 1
216:
	mov eax, 2752
	mov ecx, 2752
	mov edx, 2752
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 216b
	mov eax, 2752
	mov ecx, 2752
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 223
217:
	mov eax, 2752
	mov ecx, 2752
	mov edx, 2752
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 217b
	mov eax, 2752
	mov ecx, 2752
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 832
	mov edx, 2752
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 832
	mov edx, 832
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 448
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1600]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+1604]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+1608]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+1612]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+1616]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+1620]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+1624]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+1628]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+1632]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+1636]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+1640]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+1644]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+1648]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+1652]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+1656]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+1660]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+1664]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+1668]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+1672]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+1676]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+1680]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+1684]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+1688]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+1692]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+1696]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+1700]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+1704]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+1708]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3892], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3896], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3900], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3904], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3908], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3912], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3916], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3920], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3924], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3928], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3932], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3936], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3940], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3944], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3948], eax
	mov eax, DWORD PTR [edi+3840]
	add eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+3896]
	add eax, 1
	mov DWORD PTR [edi+3896], eax
	mov ebx, 0
	mov eax, DWORD PTR [edi+3840]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3840], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3844]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3844], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3848]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3848], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3852]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3852], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3856]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3856], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3860]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3860], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3864]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3864], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3868]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3868], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3872]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3872], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3876]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3876], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3880]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3880], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3884]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3884], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3888]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3888], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3892]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3892], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3896]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3896], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3900]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3900], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3904]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3904], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3908]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3908], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3912]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3912], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3916]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3916], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3920]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3920], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3924]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3924], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3928]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3928], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3932]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3932], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3936]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3936], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3940]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3940], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3944]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3944], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3948]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3948], edx
	shr ebx, 16
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+3840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+3844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+3848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+3852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+3856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+3860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+3864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+3868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+3872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+3876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+3880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+3884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+3888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+3892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+3896]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+3900]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+3904]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+3908]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+3912]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+3916]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+3920]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+3924]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+3928]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+3932]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+3936]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+3940]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+3944]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+3948]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+1600], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+1604], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+1608], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+1612], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+1616], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+1620], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+1624], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+1628], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+1632], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+1636], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+1640], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+1644], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+1648], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+1652], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+1656], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+1660], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+1664], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+1668], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+1672], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+1676], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+1680], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+1684], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+1688], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+1692], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+1696], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+1700], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+1704], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+1708], eax
	mov eax, DWORD PTR [edi+1728]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+1732]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+1736]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+1740]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+1744]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+1748]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+1752]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+1784]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+1788]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+1792]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+1796]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+1800]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+1804]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+1808]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+1812]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+1832]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+1836]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3892], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3896], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3900], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3904], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3908], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3912], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3916], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3920], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3924], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3928], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3932], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3936], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3940], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3944], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3948], eax
	mov eax, DWORD PTR [edi+3840]
	add eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+3896]
	add eax, 1
	mov DWORD PTR [edi+3896], eax
	mov ebx, 0
	mov eax, DWORD PTR [edi+3840]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3840], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3844]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3844], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3848]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3848], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3852]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3852], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3856]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3856], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3860]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3860], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3864]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3864], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3868]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3868], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3872]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3872], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3876]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3876], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3880]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3880], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3884]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3884], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3888]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3888], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3892]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3892], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3896]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3896], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3900]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3900], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3904]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3904], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3908]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3908], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3912]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3912], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3916]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3916], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3920]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3920], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3924]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3924], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3928]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3928], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3932]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3932], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3936]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3936], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3940]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3940], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3944]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3944], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3948]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3948], edx
	shr ebx, 16
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+3840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+3844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+3848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+3852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+3856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+3860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+3864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+3868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+3872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+3876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+3880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+3884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+3888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+3892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+3896]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+3900]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+3904]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+3908]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+3912]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+3916]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+3920]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+3924]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+3928]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+3932]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+3936]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+3940]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+3944]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+3948]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+300], eax
	mov ecx, 0
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [edi+1600]
	or ecx, eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [edi+1604]
	or ecx, eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [edi+1608]
	or ecx, eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [edi+1612]
	or ecx, eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [edi+1616]
	or ecx, eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [edi+1620]
	or ecx, eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [edi+1624]
	or ecx, eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [edi+1628]
	or ecx, eax
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [edi+1632]
	or ecx, eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [edi+1636]
	or ecx, eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [edi+1640]
	or ecx, eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [edi+1644]
	or ecx, eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [edi+1648]
	or ecx, eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [edi+1652]
	or ecx, eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [edi+1656]
	or ecx, eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [edi+1660]
	or ecx, eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [edi+1664]
	or ecx, eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [edi+1668]
	or ecx, eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [edi+1672]
	or ecx, eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [edi+1676]
	or ecx, eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [edi+1680]
	or ecx, eax
	mov eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [edi+1684]
	or ecx, eax
	mov eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [edi+1688]
	or ecx, eax
	mov eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [edi+1692]
	or ecx, eax
	mov eax, DWORD PTR [edi+288]
	xor eax, DWORD PTR [edi+1696]
	or ecx, eax
	mov eax, DWORD PTR [edi+292]
	xor eax, DWORD PTR [edi+1700]
	or ecx, eax
	mov eax, DWORD PTR [edi+296]
	xor eax, DWORD PTR [edi+1704]
	or ecx, eax
	mov eax, DWORD PTR [edi+300]
	xor eax, DWORD PTR [edi+1708]
	or ecx, eax
	or ecx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+16], ecx
	mov eax, 1600
	mov ecx, 832
	mov edx, 832
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	mov edx, 832
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+832]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+836]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+856]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+860]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+864]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+868]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+880]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+884]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+888]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+892]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+896]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+900]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+904]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+908]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+912]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+916]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+920]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+924]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+928]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+932]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+936]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+940]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3892], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3896], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3900], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3904], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3908], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3912], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3916], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3920], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3924], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3928], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3932], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3936], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3940], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3944], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3948], eax
	mov eax, DWORD PTR [edi+3840]
	add eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+3896]
	add eax, 1
	mov DWORD PTR [edi+3896], eax
	mov ebx, 0
	mov eax, DWORD PTR [edi+3840]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3840], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3844]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3844], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3848]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3848], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3852]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3852], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3856]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3856], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3860]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3860], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3864]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3864], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3868]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3868], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3872]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3872], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3876]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3876], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3880]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3880], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3884]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3884], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3888]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3888], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3892]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3892], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3896]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3896], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3900]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3900], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3904]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3904], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3908]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3908], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3912]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3912], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3916]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3916], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3920]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3920], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3924]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3924], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3928]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3928], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3932]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3932], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3936]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3936], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3940]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3940], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3944]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3944], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3948]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3948], edx
	shr ebx, 16
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+3840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+3844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+3848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+3852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+3856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+3860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+3864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+3868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+3872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+3876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+3880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+3884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+3888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+3892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+3896]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+3900]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+3904]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+3908]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+3912]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+3916]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+3920]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+3924]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+3928]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+3932]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+3936]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+3940]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+3944]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+3948]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+300], eax
	mov edx, DWORD PTR [edi+192]
	or edx, DWORD PTR [edi+196]
	or edx, DWORD PTR [edi+200]
	or edx, DWORD PTR [edi+204]
	or edx, DWORD PTR [edi+208]
	or edx, DWORD PTR [edi+212]
	or edx, DWORD PTR [edi+216]
	or edx, DWORD PTR [edi+220]
	or edx, DWORD PTR [edi+224]
	or edx, DWORD PTR [edi+228]
	or edx, DWORD PTR [edi+232]
	or edx, DWORD PTR [edi+236]
	or edx, DWORD PTR [edi+240]
	or edx, DWORD PTR [edi+244]
	or edx, DWORD PTR [edi+248]
	or edx, DWORD PTR [edi+252]
	or edx, DWORD PTR [edi+256]
	or edx, DWORD PTR [edi+260]
	or edx, DWORD PTR [edi+264]
	or edx, DWORD PTR [edi+268]
	or edx, DWORD PTR [edi+272]
	or edx, DWORD PTR [edi+276]
	or edx, DWORD PTR [edi+280]
	or edx, DWORD PTR [edi+284]
	or edx, DWORD PTR [edi+288]
	or edx, DWORD PTR [edi+292]
	or edx, DWORD PTR [edi+296]
	or edx, DWORD PTR [edi+300]
	sub edx, 1
	shr edx, 31
	and edx, DWORD PTR [edi+20]
	or edx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+16], edx
	mov eax, DWORD PTR [edi+192]
	and eax, 1
	xor eax, DWORD PTR [edi+20]
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [edi+832]
	mov ecx, DWORD PTR [edi+1600]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+832], eax
	mov DWORD PTR [edi+1600], ecx
	mov eax, DWORD PTR [edi+836]
	mov ecx, DWORD PTR [edi+1604]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+836], eax
	mov DWORD PTR [edi+1604], ecx
	mov eax, DWORD PTR [edi+840]
	mov ecx, DWORD PTR [edi+1608]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+840], eax
	mov DWORD PTR [edi+1608], ecx
	mov eax, DWORD PTR [edi+844]
	mov ecx, DWORD PTR [edi+1612]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+844], eax
	mov DWORD PTR [edi+1612], ecx
	mov eax, DWORD PTR [edi+848]
	mov ecx, DWORD PTR [edi+1616]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+848], eax
	mov DWORD PTR [edi+1616], ecx
	mov eax, DWORD PTR [edi+852]
	mov ecx, DWORD PTR [edi+1620]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+852], eax
	mov DWORD PTR [edi+1620], ecx
	mov eax, DWORD PTR [edi+856]
	mov ecx, DWORD PTR [edi+1624]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+856], eax
	mov DWORD PTR [edi+1624], ecx
	mov eax, DWORD PTR [edi+860]
	mov ecx, DWORD PTR [edi+1628]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+860], eax
	mov DWORD PTR [edi+1628], ecx
	mov eax, DWORD PTR [edi+864]
	mov ecx, DWORD PTR [edi+1632]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+864], eax
	mov DWORD PTR [edi+1632], ecx
	mov eax, DWORD PTR [edi+868]
	mov ecx, DWORD PTR [edi+1636]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+868], eax
	mov DWORD PTR [edi+1636], ecx
	mov eax, DWORD PTR [edi+872]
	mov ecx, DWORD PTR [edi+1640]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+872], eax
	mov DWORD PTR [edi+1640], ecx
	mov eax, DWORD PTR [edi+876]
	mov ecx, DWORD PTR [edi+1644]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+876], eax
	mov DWORD PTR [edi+1644], ecx
	mov eax, DWORD PTR [edi+880]
	mov ecx, DWORD PTR [edi+1648]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+880], eax
	mov DWORD PTR [edi+1648], ecx
	mov eax, DWORD PTR [edi+884]
	mov ecx, DWORD PTR [edi+1652]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+884], eax
	mov DWORD PTR [edi+1652], ecx
	mov eax, DWORD PTR [edi+888]
	mov ecx, DWORD PTR [edi+1656]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+888], eax
	mov DWORD PTR [edi+1656], ecx
	mov eax, DWORD PTR [edi+892]
	mov ecx, DWORD PTR [edi+1660]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+892], eax
	mov DWORD PTR [edi+1660], ecx
	mov eax, DWORD PTR [edi+896]
	mov ecx, DWORD PTR [edi+1664]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+896], eax
	mov DWORD PTR [edi+1664], ecx
	mov eax, DWORD PTR [edi+900]
	mov ecx, DWORD PTR [edi+1668]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+900], eax
	mov DWORD PTR [edi+1668], ecx
	mov eax, DWORD PTR [edi+904]
	mov ecx, DWORD PTR [edi+1672]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+904], eax
	mov DWORD PTR [edi+1672], ecx
	mov eax, DWORD PTR [edi+908]
	mov ecx, DWORD PTR [edi+1676]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+908], eax
	mov DWORD PTR [edi+1676], ecx
	mov eax, DWORD PTR [edi+912]
	mov ecx, DWORD PTR [edi+1680]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+912], eax
	mov DWORD PTR [edi+1680], ecx
	mov eax, DWORD PTR [edi+916]
	mov ecx, DWORD PTR [edi+1684]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+916], eax
	mov DWORD PTR [edi+1684], ecx
	mov eax, DWORD PTR [edi+920]
	mov ecx, DWORD PTR [edi+1688]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+920], eax
	mov DWORD PTR [edi+1688], ecx
	mov eax, DWORD PTR [edi+924]
	mov ecx, DWORD PTR [edi+1692]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+924], eax
	mov DWORD PTR [edi+1692], ecx
	mov eax, DWORD PTR [edi+928]
	mov ecx, DWORD PTR [edi+1696]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+928], eax
	mov DWORD PTR [edi+1696], ecx
	mov eax, DWORD PTR [edi+932]
	mov ecx, DWORD PTR [edi+1700]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+932], eax
	mov DWORD PTR [edi+1700], ecx
	mov eax, DWORD PTR [edi+936]
	mov ecx, DWORD PTR [edi+1704]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+936], eax
	mov DWORD PTR [edi+1704], ecx
	mov eax, DWORD PTR [edi+940]
	mov ecx, DWORD PTR [edi+1708]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+940], eax
	mov DWORD PTR [edi+1708], ecx
	mov esi, DWORD PTR [esp+4]
	mov DWORD PTR [edi+4352], esi
	mov ebx, DWORD PTR [edi+4356]
	sub ebx, 1
	mov DWORD PTR [edi+4356], ebx
	jne 23b
	mov eax, 832
	mov ecx, 64
	mov edx, 832
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1344]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+1348]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+1352]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+1356]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+1360]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+1364]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+1368]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+1372]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+1376]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+1380]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+1384]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+1388]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+1392]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+1396]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+1400]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+1404]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+1408]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+1412]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+1416]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+1420]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+1424]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+1428]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+1432]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+1436]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+1440]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+1444]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+1448]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+1452]
	mov DWORD PTR [edi+300], eax
	mov esi, 456
218:
	sub esi, 1
	mov eax, 1600
	mov ecx, 64
	mov edx, 192
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 64
	mov edx, 64
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 192
	mov edx, 192
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 320
	mov edx, 320
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 2112
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 1600
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 64
	mov ecx, 2368
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 192
	mov ecx, 1984
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 320
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 320
	mov edx, 1344
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1600
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 64
	mov edx, 1088
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 192
	mov edx, 1216
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 1472
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 2112
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 1728
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 1728
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 64
	mov edx, 192
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 1088
	mov edx, 1216
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 1600
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 1600
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 1984
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 2240
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, edi
	add ebp, esi
	movzx eax, BYTE PTR [ebp+3072]
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [edi+64]
	mov ecx, DWORD PTR [edi+448]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+64], eax
	mov DWORD PTR [edi+448], ecx
	mov eax, DWORD PTR [edi+68]
	mov ecx, DWORD PTR [edi+452]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+68], eax
	mov DWORD PTR [edi+452], ecx
	mov eax, DWORD PTR [edi+72]
	mov ecx, DWORD PTR [edi+456]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+72], eax
	mov DWORD PTR [edi+456], ecx
	mov eax, DWORD PTR [edi+76]
	mov ecx, DWORD PTR [edi+460]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+76], eax
	mov DWORD PTR [edi+460], ecx
	mov eax, DWORD PTR [edi+80]
	mov ecx, DWORD PTR [edi+464]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+80], eax
	mov DWORD PTR [edi+464], ecx
	mov eax, DWORD PTR [edi+84]
	mov ecx, DWORD PTR [edi+468]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+84], eax
	mov DWORD PTR [edi+468], ecx
	mov eax, DWORD PTR [edi+88]
	mov ecx, DWORD PTR [edi+472]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+88], eax
	mov DWORD PTR [edi+472], ecx
	mov eax, DWORD PTR [edi+92]
	mov ecx, DWORD PTR [edi+476]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+92], eax
	mov DWORD PTR [edi+476], ecx
	mov eax, DWORD PTR [edi+96]
	mov ecx, DWORD PTR [edi+480]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+96], eax
	mov DWORD PTR [edi+480], ecx
	mov eax, DWORD PTR [edi+100]
	mov ecx, DWORD PTR [edi+484]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+100], eax
	mov DWORD PTR [edi+484], ecx
	mov eax, DWORD PTR [edi+104]
	mov ecx, DWORD PTR [edi+488]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+104], eax
	mov DWORD PTR [edi+488], ecx
	mov eax, DWORD PTR [edi+108]
	mov ecx, DWORD PTR [edi+492]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+108], eax
	mov DWORD PTR [edi+492], ecx
	mov eax, DWORD PTR [edi+112]
	mov ecx, DWORD PTR [edi+496]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+112], eax
	mov DWORD PTR [edi+496], ecx
	mov eax, DWORD PTR [edi+116]
	mov ecx, DWORD PTR [edi+500]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+116], eax
	mov DWORD PTR [edi+500], ecx
	mov eax, DWORD PTR [edi+120]
	mov ecx, DWORD PTR [edi+504]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+120], eax
	mov DWORD PTR [edi+504], ecx
	mov eax, DWORD PTR [edi+124]
	mov ecx, DWORD PTR [edi+508]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+124], eax
	mov DWORD PTR [edi+508], ecx
	mov eax, DWORD PTR [edi+128]
	mov ecx, DWORD PTR [edi+512]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+128], eax
	mov DWORD PTR [edi+512], ecx
	mov eax, DWORD PTR [edi+132]
	mov ecx, DWORD PTR [edi+516]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+132], eax
	mov DWORD PTR [edi+516], ecx
	mov eax, DWORD PTR [edi+136]
	mov ecx, DWORD PTR [edi+520]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+136], eax
	mov DWORD PTR [edi+520], ecx
	mov eax, DWORD PTR [edi+140]
	mov ecx, DWORD PTR [edi+524]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+140], eax
	mov DWORD PTR [edi+524], ecx
	mov eax, DWORD PTR [edi+144]
	mov ecx, DWORD PTR [edi+528]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+144], eax
	mov DWORD PTR [edi+528], ecx
	mov eax, DWORD PTR [edi+148]
	mov ecx, DWORD PTR [edi+532]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+148], eax
	mov DWORD PTR [edi+532], ecx
	mov eax, DWORD PTR [edi+152]
	mov ecx, DWORD PTR [edi+536]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+152], eax
	mov DWORD PTR [edi+536], ecx
	mov eax, DWORD PTR [edi+156]
	mov ecx, DWORD PTR [edi+540]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+156], eax
	mov DWORD PTR [edi+540], ecx
	mov eax, DWORD PTR [edi+160]
	mov ecx, DWORD PTR [edi+544]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+160], eax
	mov DWORD PTR [edi+544], ecx
	mov eax, DWORD PTR [edi+164]
	mov ecx, DWORD PTR [edi+548]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+164], eax
	mov DWORD PTR [edi+548], ecx
	mov eax, DWORD PTR [edi+168]
	mov ecx, DWORD PTR [edi+552]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+168], eax
	mov DWORD PTR [edi+552], ecx
	mov eax, DWORD PTR [edi+172]
	mov ecx, DWORD PTR [edi+556]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+172], eax
	mov DWORD PTR [edi+556], ecx
	mov eax, DWORD PTR [edi+192]
	mov ecx, DWORD PTR [edi+576]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+192], eax
	mov DWORD PTR [edi+576], ecx
	mov eax, DWORD PTR [edi+196]
	mov ecx, DWORD PTR [edi+580]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+196], eax
	mov DWORD PTR [edi+580], ecx
	mov eax, DWORD PTR [edi+200]
	mov ecx, DWORD PTR [edi+584]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+200], eax
	mov DWORD PTR [edi+584], ecx
	mov eax, DWORD PTR [edi+204]
	mov ecx, DWORD PTR [edi+588]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+204], eax
	mov DWORD PTR [edi+588], ecx
	mov eax, DWORD PTR [edi+208]
	mov ecx, DWORD PTR [edi+592]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+208], eax
	mov DWORD PTR [edi+592], ecx
	mov eax, DWORD PTR [edi+212]
	mov ecx, DWORD PTR [edi+596]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+212], eax
	mov DWORD PTR [edi+596], ecx
	mov eax, DWORD PTR [edi+216]
	mov ecx, DWORD PTR [edi+600]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+216], eax
	mov DWORD PTR [edi+600], ecx
	mov eax, DWORD PTR [edi+220]
	mov ecx, DWORD PTR [edi+604]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+220], eax
	mov DWORD PTR [edi+604], ecx
	mov eax, DWORD PTR [edi+224]
	mov ecx, DWORD PTR [edi+608]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+224], eax
	mov DWORD PTR [edi+608], ecx
	mov eax, DWORD PTR [edi+228]
	mov ecx, DWORD PTR [edi+612]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+228], eax
	mov DWORD PTR [edi+612], ecx
	mov eax, DWORD PTR [edi+232]
	mov ecx, DWORD PTR [edi+616]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+232], eax
	mov DWORD PTR [edi+616], ecx
	mov eax, DWORD PTR [edi+236]
	mov ecx, DWORD PTR [edi+620]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+236], eax
	mov DWORD PTR [edi+620], ecx
	mov eax, DWORD PTR [edi+240]
	mov ecx, DWORD PTR [edi+624]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+240], eax
	mov DWORD PTR [edi+624], ecx
	mov eax, DWORD PTR [edi+244]
	mov ecx, DWORD PTR [edi+628]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+244], eax
	mov DWORD PTR [edi+628], ecx
	mov eax, DWORD PTR [edi+248]
	mov ecx, DWORD PTR [edi+632]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+248], eax
	mov DWORD PTR [edi+632], ecx
	mov eax, DWORD PTR [edi+252]
	mov ecx, DWORD PTR [edi+636]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+252], eax
	mov DWORD PTR [edi+636], ecx
	mov eax, DWORD PTR [edi+256]
	mov ecx, DWORD PTR [edi+640]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+256], eax
	mov DWORD PTR [edi+640], ecx
	mov eax, DWORD PTR [edi+260]
	mov ecx, DWORD PTR [edi+644]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+260], eax
	mov DWORD PTR [edi+644], ecx
	mov eax, DWORD PTR [edi+264]
	mov ecx, DWORD PTR [edi+648]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+264], eax
	mov DWORD PTR [edi+648], ecx
	mov eax, DWORD PTR [edi+268]
	mov ecx, DWORD PTR [edi+652]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+268], eax
	mov DWORD PTR [edi+652], ecx
	mov eax, DWORD PTR [edi+272]
	mov ecx, DWORD PTR [edi+656]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+272], eax
	mov DWORD PTR [edi+656], ecx
	mov eax, DWORD PTR [edi+276]
	mov ecx, DWORD PTR [edi+660]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+276], eax
	mov DWORD PTR [edi+660], ecx
	mov eax, DWORD PTR [edi+280]
	mov ecx, DWORD PTR [edi+664]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+280], eax
	mov DWORD PTR [edi+664], ecx
	mov eax, DWORD PTR [edi+284]
	mov ecx, DWORD PTR [edi+668]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+284], eax
	mov DWORD PTR [edi+668], ecx
	mov eax, DWORD PTR [edi+288]
	mov ecx, DWORD PTR [edi+672]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+288], eax
	mov DWORD PTR [edi+672], ecx
	mov eax, DWORD PTR [edi+292]
	mov ecx, DWORD PTR [edi+676]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+292], eax
	mov DWORD PTR [edi+676], ecx
	mov eax, DWORD PTR [edi+296]
	mov ecx, DWORD PTR [edi+680]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+296], eax
	mov DWORD PTR [edi+680], ecx
	mov eax, DWORD PTR [edi+300]
	mov ecx, DWORD PTR [edi+684]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+300], eax
	mov DWORD PTR [edi+684], ecx
	mov eax, DWORD PTR [edi+320]
	mov ecx, DWORD PTR [edi+704]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+320], eax
	mov DWORD PTR [edi+704], ecx
	mov eax, DWORD PTR [edi+324]
	mov ecx, DWORD PTR [edi+708]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+324], eax
	mov DWORD PTR [edi+708], ecx
	mov eax, DWORD PTR [edi+328]
	mov ecx, DWORD PTR [edi+712]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+328], eax
	mov DWORD PTR [edi+712], ecx
	mov eax, DWORD PTR [edi+332]
	mov ecx, DWORD PTR [edi+716]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+332], eax
	mov DWORD PTR [edi+716], ecx
	mov eax, DWORD PTR [edi+336]
	mov ecx, DWORD PTR [edi+720]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+336], eax
	mov DWORD PTR [edi+720], ecx
	mov eax, DWORD PTR [edi+340]
	mov ecx, DWORD PTR [edi+724]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+340], eax
	mov DWORD PTR [edi+724], ecx
	mov eax, DWORD PTR [edi+344]
	mov ecx, DWORD PTR [edi+728]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+344], eax
	mov DWORD PTR [edi+728], ecx
	mov eax, DWORD PTR [edi+348]
	mov ecx, DWORD PTR [edi+732]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+348], eax
	mov DWORD PTR [edi+732], ecx
	mov eax, DWORD PTR [edi+352]
	mov ecx, DWORD PTR [edi+736]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+352], eax
	mov DWORD PTR [edi+736], ecx
	mov eax, DWORD PTR [edi+356]
	mov ecx, DWORD PTR [edi+740]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+356], eax
	mov DWORD PTR [edi+740], ecx
	mov eax, DWORD PTR [edi+360]
	mov ecx, DWORD PTR [edi+744]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+360], eax
	mov DWORD PTR [edi+744], ecx
	mov eax, DWORD PTR [edi+364]
	mov ecx, DWORD PTR [edi+748]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+364], eax
	mov DWORD PTR [edi+748], ecx
	mov eax, DWORD PTR [edi+368]
	mov ecx, DWORD PTR [edi+752]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+368], eax
	mov DWORD PTR [edi+752], ecx
	mov eax, DWORD PTR [edi+372]
	mov ecx, DWORD PTR [edi+756]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+372], eax
	mov DWORD PTR [edi+756], ecx
	mov eax, DWORD PTR [edi+376]
	mov ecx, DWORD PTR [edi+760]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+376], eax
	mov DWORD PTR [edi+760], ecx
	mov eax, DWORD PTR [edi+380]
	mov ecx, DWORD PTR [edi+764]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+380], eax
	mov DWORD PTR [edi+764], ecx
	mov eax, DWORD PTR [edi+384]
	mov ecx, DWORD PTR [edi+768]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+384], eax
	mov DWORD PTR [edi+768], ecx
	mov eax, DWORD PTR [edi+388]
	mov ecx, DWORD PTR [edi+772]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+388], eax
	mov DWORD PTR [edi+772], ecx
	mov eax, DWORD PTR [edi+392]
	mov ecx, DWORD PTR [edi+776]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+392], eax
	mov DWORD PTR [edi+776], ecx
	mov eax, DWORD PTR [edi+396]
	mov ecx, DWORD PTR [edi+780]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+396], eax
	mov DWORD PTR [edi+780], ecx
	mov eax, DWORD PTR [edi+400]
	mov ecx, DWORD PTR [edi+784]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+400], eax
	mov DWORD PTR [edi+784], ecx
	mov eax, DWORD PTR [edi+404]
	mov ecx, DWORD PTR [edi+788]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+404], eax
	mov DWORD PTR [edi+788], ecx
	mov eax, DWORD PTR [edi+408]
	mov ecx, DWORD PTR [edi+792]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+792], ecx
	mov eax, DWORD PTR [edi+412]
	mov ecx, DWORD PTR [edi+796]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+412], eax
	mov DWORD PTR [edi+796], ecx
	mov eax, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [edi+800]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+800], ecx
	mov eax, DWORD PTR [edi+420]
	mov ecx, DWORD PTR [edi+804]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+420], eax
	mov DWORD PTR [edi+804], ecx
	mov eax, DWORD PTR [edi+424]
	mov ecx, DWORD PTR [edi+808]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+808], ecx
	mov eax, DWORD PTR [edi+428]
	mov ecx, DWORD PTR [edi+812]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+428], eax
	mov DWORD PTR [edi+812], ecx
	mov eax, 1600
	mov ecx, 320
	mov edx, 1344
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1600
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 64
	mov edx, 832
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 192
	mov edx, 960
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 1472
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 2112
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 1728
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 1728
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 64
	mov edx, 192
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 832
	mov edx, 960
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 1600
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 1600
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 1984
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 2240
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, edi
	add ebp, esi
	movzx eax, BYTE PTR [ebp+4608]
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [edi+64]
	mov ecx, DWORD PTR [edi+448]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+64], eax
	mov DWORD PTR [edi+448], ecx
	mov eax, DWORD PTR [edi+68]
	mov ecx, DWORD PTR [edi+452]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+68], eax
	mov DWORD PTR [edi+452], ecx
	mov eax, DWORD PTR [edi+72]
	mov ecx, DWORD PTR [edi+456]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+72], eax
	mov DWORD PTR [edi+456], ecx
	mov eax, DWORD PTR [edi+76]
	mov ecx, DWORD PTR [edi+460]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+76], eax
	mov DWORD PTR [edi+460], ecx
	mov eax, DWORD PTR [edi+80]
	mov ecx, DWORD PTR [edi+464]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+80], eax
	mov DWORD PTR [edi+464], ecx
	mov eax, DWORD PTR [edi+84]
	mov ecx, DWORD PTR [edi+468]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+84], eax
	mov DWORD PTR [edi+468], ecx
	mov eax, DWORD PTR [edi+88]
	mov ecx, DWORD PTR [edi+472]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+88], eax
	mov DWORD PTR [edi+472], ecx
	mov eax, DWORD PTR [edi+92]
	mov ecx, DWORD PTR [edi+476]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+92], eax
	mov DWORD PTR [edi+476], ecx
	mov eax, DWORD PTR [edi+96]
	mov ecx, DWORD PTR [edi+480]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+96], eax
	mov DWORD PTR [edi+480], ecx
	mov eax, DWORD PTR [edi+100]
	mov ecx, DWORD PTR [edi+484]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+100], eax
	mov DWORD PTR [edi+484], ecx
	mov eax, DWORD PTR [edi+104]
	mov ecx, DWORD PTR [edi+488]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+104], eax
	mov DWORD PTR [edi+488], ecx
	mov eax, DWORD PTR [edi+108]
	mov ecx, DWORD PTR [edi+492]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+108], eax
	mov DWORD PTR [edi+492], ecx
	mov eax, DWORD PTR [edi+112]
	mov ecx, DWORD PTR [edi+496]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+112], eax
	mov DWORD PTR [edi+496], ecx
	mov eax, DWORD PTR [edi+116]
	mov ecx, DWORD PTR [edi+500]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+116], eax
	mov DWORD PTR [edi+500], ecx
	mov eax, DWORD PTR [edi+120]
	mov ecx, DWORD PTR [edi+504]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+120], eax
	mov DWORD PTR [edi+504], ecx
	mov eax, DWORD PTR [edi+124]
	mov ecx, DWORD PTR [edi+508]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+124], eax
	mov DWORD PTR [edi+508], ecx
	mov eax, DWORD PTR [edi+128]
	mov ecx, DWORD PTR [edi+512]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+128], eax
	mov DWORD PTR [edi+512], ecx
	mov eax, DWORD PTR [edi+132]
	mov ecx, DWORD PTR [edi+516]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+132], eax
	mov DWORD PTR [edi+516], ecx
	mov eax, DWORD PTR [edi+136]
	mov ecx, DWORD PTR [edi+520]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+136], eax
	mov DWORD PTR [edi+520], ecx
	mov eax, DWORD PTR [edi+140]
	mov ecx, DWORD PTR [edi+524]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+140], eax
	mov DWORD PTR [edi+524], ecx
	mov eax, DWORD PTR [edi+144]
	mov ecx, DWORD PTR [edi+528]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+144], eax
	mov DWORD PTR [edi+528], ecx
	mov eax, DWORD PTR [edi+148]
	mov ecx, DWORD PTR [edi+532]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+148], eax
	mov DWORD PTR [edi+532], ecx
	mov eax, DWORD PTR [edi+152]
	mov ecx, DWORD PTR [edi+536]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+152], eax
	mov DWORD PTR [edi+536], ecx
	mov eax, DWORD PTR [edi+156]
	mov ecx, DWORD PTR [edi+540]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+156], eax
	mov DWORD PTR [edi+540], ecx
	mov eax, DWORD PTR [edi+160]
	mov ecx, DWORD PTR [edi+544]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+160], eax
	mov DWORD PTR [edi+544], ecx
	mov eax, DWORD PTR [edi+164]
	mov ecx, DWORD PTR [edi+548]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+164], eax
	mov DWORD PTR [edi+548], ecx
	mov eax, DWORD PTR [edi+168]
	mov ecx, DWORD PTR [edi+552]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+168], eax
	mov DWORD PTR [edi+552], ecx
	mov eax, DWORD PTR [edi+172]
	mov ecx, DWORD PTR [edi+556]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+172], eax
	mov DWORD PTR [edi+556], ecx
	mov eax, DWORD PTR [edi+192]
	mov ecx, DWORD PTR [edi+576]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+192], eax
	mov DWORD PTR [edi+576], ecx
	mov eax, DWORD PTR [edi+196]
	mov ecx, DWORD PTR [edi+580]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+196], eax
	mov DWORD PTR [edi+580], ecx
	mov eax, DWORD PTR [edi+200]
	mov ecx, DWORD PTR [edi+584]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+200], eax
	mov DWORD PTR [edi+584], ecx
	mov eax, DWORD PTR [edi+204]
	mov ecx, DWORD PTR [edi+588]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+204], eax
	mov DWORD PTR [edi+588], ecx
	mov eax, DWORD PTR [edi+208]
	mov ecx, DWORD PTR [edi+592]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+208], eax
	mov DWORD PTR [edi+592], ecx
	mov eax, DWORD PTR [edi+212]
	mov ecx, DWORD PTR [edi+596]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+212], eax
	mov DWORD PTR [edi+596], ecx
	mov eax, DWORD PTR [edi+216]
	mov ecx, DWORD PTR [edi+600]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+216], eax
	mov DWORD PTR [edi+600], ecx
	mov eax, DWORD PTR [edi+220]
	mov ecx, DWORD PTR [edi+604]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+220], eax
	mov DWORD PTR [edi+604], ecx
	mov eax, DWORD PTR [edi+224]
	mov ecx, DWORD PTR [edi+608]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+224], eax
	mov DWORD PTR [edi+608], ecx
	mov eax, DWORD PTR [edi+228]
	mov ecx, DWORD PTR [edi+612]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+228], eax
	mov DWORD PTR [edi+612], ecx
	mov eax, DWORD PTR [edi+232]
	mov ecx, DWORD PTR [edi+616]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+232], eax
	mov DWORD PTR [edi+616], ecx
	mov eax, DWORD PTR [edi+236]
	mov ecx, DWORD PTR [edi+620]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+236], eax
	mov DWORD PTR [edi+620], ecx
	mov eax, DWORD PTR [edi+240]
	mov ecx, DWORD PTR [edi+624]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+240], eax
	mov DWORD PTR [edi+624], ecx
	mov eax, DWORD PTR [edi+244]
	mov ecx, DWORD PTR [edi+628]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+244], eax
	mov DWORD PTR [edi+628], ecx
	mov eax, DWORD PTR [edi+248]
	mov ecx, DWORD PTR [edi+632]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+248], eax
	mov DWORD PTR [edi+632], ecx
	mov eax, DWORD PTR [edi+252]
	mov ecx, DWORD PTR [edi+636]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+252], eax
	mov DWORD PTR [edi+636], ecx
	mov eax, DWORD PTR [edi+256]
	mov ecx, DWORD PTR [edi+640]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+256], eax
	mov DWORD PTR [edi+640], ecx
	mov eax, DWORD PTR [edi+260]
	mov ecx, DWORD PTR [edi+644]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+260], eax
	mov DWORD PTR [edi+644], ecx
	mov eax, DWORD PTR [edi+264]
	mov ecx, DWORD PTR [edi+648]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+264], eax
	mov DWORD PTR [edi+648], ecx
	mov eax, DWORD PTR [edi+268]
	mov ecx, DWORD PTR [edi+652]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+268], eax
	mov DWORD PTR [edi+652], ecx
	mov eax, DWORD PTR [edi+272]
	mov ecx, DWORD PTR [edi+656]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+272], eax
	mov DWORD PTR [edi+656], ecx
	mov eax, DWORD PTR [edi+276]
	mov ecx, DWORD PTR [edi+660]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+276], eax
	mov DWORD PTR [edi+660], ecx
	mov eax, DWORD PTR [edi+280]
	mov ecx, DWORD PTR [edi+664]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+280], eax
	mov DWORD PTR [edi+664], ecx
	mov eax, DWORD PTR [edi+284]
	mov ecx, DWORD PTR [edi+668]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+284], eax
	mov DWORD PTR [edi+668], ecx
	mov eax, DWORD PTR [edi+288]
	mov ecx, DWORD PTR [edi+672]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+288], eax
	mov DWORD PTR [edi+672], ecx
	mov eax, DWORD PTR [edi+292]
	mov ecx, DWORD PTR [edi+676]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+292], eax
	mov DWORD PTR [edi+676], ecx
	mov eax, DWORD PTR [edi+296]
	mov ecx, DWORD PTR [edi+680]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+296], eax
	mov DWORD PTR [edi+680], ecx
	mov eax, DWORD PTR [edi+300]
	mov ecx, DWORD PTR [edi+684]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+300], eax
	mov DWORD PTR [edi+684], ecx
	mov eax, DWORD PTR [edi+320]
	mov ecx, DWORD PTR [edi+704]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+320], eax
	mov DWORD PTR [edi+704], ecx
	mov eax, DWORD PTR [edi+324]
	mov ecx, DWORD PTR [edi+708]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+324], eax
	mov DWORD PTR [edi+708], ecx
	mov eax, DWORD PTR [edi+328]
	mov ecx, DWORD PTR [edi+712]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+328], eax
	mov DWORD PTR [edi+712], ecx
	mov eax, DWORD PTR [edi+332]
	mov ecx, DWORD PTR [edi+716]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+332], eax
	mov DWORD PTR [edi+716], ecx
	mov eax, DWORD PTR [edi+336]
	mov ecx, DWORD PTR [edi+720]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+336], eax
	mov DWORD PTR [edi+720], ecx
	mov eax, DWORD PTR [edi+340]
	mov ecx, DWORD PTR [edi+724]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+340], eax
	mov DWORD PTR [edi+724], ecx
	mov eax, DWORD PTR [edi+344]
	mov ecx, DWORD PTR [edi+728]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+344], eax
	mov DWORD PTR [edi+728], ecx
	mov eax, DWORD PTR [edi+348]
	mov ecx, DWORD PTR [edi+732]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+348], eax
	mov DWORD PTR [edi+732], ecx
	mov eax, DWORD PTR [edi+352]
	mov ecx, DWORD PTR [edi+736]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+352], eax
	mov DWORD PTR [edi+736], ecx
	mov eax, DWORD PTR [edi+356]
	mov ecx, DWORD PTR [edi+740]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+356], eax
	mov DWORD PTR [edi+740], ecx
	mov eax, DWORD PTR [edi+360]
	mov ecx, DWORD PTR [edi+744]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+360], eax
	mov DWORD PTR [edi+744], ecx
	mov eax, DWORD PTR [edi+364]
	mov ecx, DWORD PTR [edi+748]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+364], eax
	mov DWORD PTR [edi+748], ecx
	mov eax, DWORD PTR [edi+368]
	mov ecx, DWORD PTR [edi+752]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+368], eax
	mov DWORD PTR [edi+752], ecx
	mov eax, DWORD PTR [edi+372]
	mov ecx, DWORD PTR [edi+756]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+372], eax
	mov DWORD PTR [edi+756], ecx
	mov eax, DWORD PTR [edi+376]
	mov ecx, DWORD PTR [edi+760]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+376], eax
	mov DWORD PTR [edi+760], ecx
	mov eax, DWORD PTR [edi+380]
	mov ecx, DWORD PTR [edi+764]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+380], eax
	mov DWORD PTR [edi+764], ecx
	mov eax, DWORD PTR [edi+384]
	mov ecx, DWORD PTR [edi+768]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+384], eax
	mov DWORD PTR [edi+768], ecx
	mov eax, DWORD PTR [edi+388]
	mov ecx, DWORD PTR [edi+772]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+388], eax
	mov DWORD PTR [edi+772], ecx
	mov eax, DWORD PTR [edi+392]
	mov ecx, DWORD PTR [edi+776]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+392], eax
	mov DWORD PTR [edi+776], ecx
	mov eax, DWORD PTR [edi+396]
	mov ecx, DWORD PTR [edi+780]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+396], eax
	mov DWORD PTR [edi+780], ecx
	mov eax, DWORD PTR [edi+400]
	mov ecx, DWORD PTR [edi+784]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+400], eax
	mov DWORD PTR [edi+784], ecx
	mov eax, DWORD PTR [edi+404]
	mov ecx, DWORD PTR [edi+788]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+404], eax
	mov DWORD PTR [edi+788], ecx
	mov eax, DWORD PTR [edi+408]
	mov ecx, DWORD PTR [edi+792]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+792], ecx
	mov eax, DWORD PTR [edi+412]
	mov ecx, DWORD PTR [edi+796]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+412], eax
	mov DWORD PTR [edi+796], ecx
	mov eax, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [edi+800]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+800], ecx
	mov eax, DWORD PTR [edi+420]
	mov ecx, DWORD PTR [edi+804]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+420], eax
	mov DWORD PTR [edi+804], ecx
	mov eax, DWORD PTR [edi+424]
	mov ecx, DWORD PTR [edi+808]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+808], ecx
	mov eax, DWORD PTR [edi+428]
	mov ecx, DWORD PTR [edi+812]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+428], eax
	mov DWORD PTR [edi+812], ecx
	cmp esi, 0
	jne 218b
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+880], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+884], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+888], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+892], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+896], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+900], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+904], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+908], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+912], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+916], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+920], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+924], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+936], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+940], eax
	mov eax, DWORD PTR [edi+4096]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+4100]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+4104]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+4108]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+4112]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+4116]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+4120]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+4124]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+4128]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+4132]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+4136]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+4140]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+4144]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+4148]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+4152]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+4156]
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [edi+4160]
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [edi+4164]
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [edi+4168]
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [edi+4172]
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [edi+4176]
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [edi+4180]
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [edi+4184]
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [edi+4188]
	mov DWORD PTR [edi+1180], eax
	mov eax, DWORD PTR [edi+4192]
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [edi+4196]
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [edi+4200]
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [edi+4204]
	mov DWORD PTR [edi+1196], eax
	mov eax, DWORD PTR [edi+4224]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [edi+4228]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [edi+4232]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+4236]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+4240]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+4244]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+4248]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+4252]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [edi+4256]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+4260]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+4264]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+4268]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [edi+4272]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [edi+4276]
	mov DWORD PTR [edi+1268], eax
	mov eax, DWORD PTR [edi+4280]
	mov DWORD PTR [edi+1272], eax
	mov eax, DWORD PTR [edi+4284]
	mov DWORD PTR [edi+1276], eax
	mov eax, DWORD PTR [edi+4288]
	mov DWORD PTR [edi+1280], eax
	mov eax, DWORD PTR [edi+4292]
	mov DWORD PTR [edi+1284], eax
	mov eax, DWORD PTR [edi+4296]
	mov DWORD PTR [edi+1288], eax
	mov eax, DWORD PTR [edi+4300]
	mov DWORD PTR [edi+1292], eax
	mov eax, DWORD PTR [edi+4304]
	mov DWORD PTR [edi+1296], eax
	mov eax, DWORD PTR [edi+4308]
	mov DWORD PTR [edi+1300], eax
	mov eax, DWORD PTR [edi+4312]
	mov DWORD PTR [edi+1304], eax
	mov eax, DWORD PTR [edi+4316]
	mov DWORD PTR [edi+1308], eax
	mov eax, DWORD PTR [edi+4320]
	mov DWORD PTR [edi+1312], eax
	mov eax, DWORD PTR [edi+4324]
	mov DWORD PTR [edi+1316], eax
	mov eax, DWORD PTR [edi+4328]
	mov DWORD PTR [edi+1320], eax
	mov eax, DWORD PTR [edi+4332]
	mov DWORD PTR [edi+1324], eax
	mov esi, 2
219:
	mov eax, 1600
	mov ecx, 64
	mov edx, 832
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 64
	mov edx, 64
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 832
	mov edx, 832
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 320
	mov edx, 320
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 2112
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 1600
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 64
	mov ecx, 2368
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 1984
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 320
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1088
	mov edx, 1216
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1088
	mov edx, 1088
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1216
	mov edx, 1216
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 1344
	mov edx, 1344
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 2112
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 1600
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 2368
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1984
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 219b
	mov esi, 2
220:
	mov eax, 1600
	mov ecx, 64
	mov edx, 1344
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1088
	mov edx, 320
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1600]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+1604]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+1608]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+1612]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+1616]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+1620]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+1624]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+1628]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+1632]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+1636]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+1640]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+1644]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+1648]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+1652]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+1656]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+1660]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+1664]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+1668]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+1672]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+1676]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+1680]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+1684]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+1688]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+1692]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+1696]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+1700]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+1704]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+1708]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3892], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3896], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3900], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3904], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3908], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3912], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3916], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3920], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3924], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3928], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3932], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3936], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3940], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3944], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3948], eax
	mov eax, DWORD PTR [edi+3840]
	add eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+3896]
	add eax, 1
	mov DWORD PTR [edi+3896], eax
	mov ebx, 0
	mov eax, DWORD PTR [edi+3840]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3840], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3844]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3844], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3848]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3848], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3852]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3852], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3856]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3856], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3860]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3860], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3864]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3864], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3868]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3868], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3872]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3872], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3876]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3876], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3880]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3880], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3884]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3884], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3888]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3888], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3892]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3892], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3896]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3896], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3900]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3900], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3904]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3904], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3908]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3908], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3912]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3912], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3916]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3916], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3920]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3920], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3924]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3924], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3928]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3928], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3932]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3932], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3936]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3936], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3940]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3940], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3944]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3944], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3948]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3948], edx
	shr ebx, 16
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+3840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+3844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+3848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+3852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+3856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+3860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+3864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+3868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+3872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+3876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+3880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+3884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+3888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+3892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+3896]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+3900]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+3904]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+3908]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+3912]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+3916]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+3920]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+3924]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+3928]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+3932]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+3936]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+3940]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+3944]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+3948]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+1600], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+1604], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+1608], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+1612], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+1616], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+1620], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+1624], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+1628], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+1632], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+1636], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+1640], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+1644], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+1648], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+1652], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+1656], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+1660], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+1664], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+1668], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+1672], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+1676], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+1680], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+1684], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+1688], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+1692], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+1696], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+1700], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+1704], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+1708], eax
	mov eax, DWORD PTR [edi+1728]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+1732]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+1736]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+1740]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+1744]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+1748]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+1752]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+1784]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+1788]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+1792]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+1796]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+1800]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+1804]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+1808]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+1812]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+1832]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+1836]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3892], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3896], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3900], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3904], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3908], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3912], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3916], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3920], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3924], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3928], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3932], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3936], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3940], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3944], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3948], eax
	mov eax, DWORD PTR [edi+3840]
	add eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+3896]
	add eax, 1
	mov DWORD PTR [edi+3896], eax
	mov ebx, 0
	mov eax, DWORD PTR [edi+3840]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3840], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3844]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3844], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3848]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3848], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3852]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3852], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3856]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3856], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3860]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3860], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3864]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3864], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3868]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3868], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3872]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3872], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3876]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3876], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3880]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3880], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3884]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3884], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3888]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3888], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3892]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3892], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3896]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3896], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3900]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3900], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3904]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3904], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3908]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3908], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3912]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3912], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3916]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3916], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3920]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3920], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3924]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3924], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3928]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3928], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3932]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3932], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3936]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3936], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3940]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3940], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3944]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3944], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3948]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3948], edx
	shr ebx, 16
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+3840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+3844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+3848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+3852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+3856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+3860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+3864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+3868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+3872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+3876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+3880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+3884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+3888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+3892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+3896]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+3900]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+3904]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+3908]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+3912]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+3916]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+3920]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+3924]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+3928]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+3932]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+3936]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+3940]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+3944]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+3948]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+300], eax
	mov ecx, 0
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [edi+1600]
	or ecx, eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [edi+1604]
	or ecx, eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [edi+1608]
	or ecx, eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [edi+1612]
	or ecx, eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [edi+1616]
	or ecx, eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [edi+1620]
	or ecx, eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [edi+1624]
	or ecx, eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [edi+1628]
	or ecx, eax
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [edi+1632]
	or ecx, eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [edi+1636]
	or ecx, eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [edi+1640]
	or ecx, eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [edi+1644]
	or ecx, eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [edi+1648]
	or ecx, eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [edi+1652]
	or ecx, eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [edi+1656]
	or ecx, eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [edi+1660]
	or ecx, eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [edi+1664]
	or ecx, eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [edi+1668]
	or ecx, eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [edi+1672]
	or ecx, eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [edi+1676]
	or ecx, eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [edi+1680]
	or ecx, eax
	mov eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [edi+1684]
	or ecx, eax
	mov eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [edi+1688]
	or ecx, eax
	mov eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [edi+1692]
	or ecx, eax
	mov eax, DWORD PTR [edi+288]
	xor eax, DWORD PTR [edi+1696]
	or ecx, eax
	mov eax, DWORD PTR [edi+292]
	xor eax, DWORD PTR [edi+1700]
	or ecx, eax
	mov eax, DWORD PTR [edi+296]
	xor eax, DWORD PTR [edi+1704]
	or ecx, eax
	mov eax, DWORD PTR [edi+300]
	xor eax, DWORD PTR [edi+1708]
	or ecx, eax
	or ecx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+16], ecx
	mov eax, DWORD PTR [edi+832]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+836]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+856]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+860]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+864]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+868]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+880]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+884]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+888]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+892]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+896]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+900]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+904]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+908]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+912]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+916]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+920]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+924]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+928]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+932]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+936]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+940]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1180], eax
	mov eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1196], eax
	sub esi, 1
	jne 220b
	mov ecx, DWORD PTR [edi+16]
	sub ecx, 1
	shr ecx, 31
	mov eax, edi
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov ebp, DWORD PTR [eax+12]
	mov edi, DWORD PTR [eax+8]
	mov eax, ecx
	ret
	.p2align 6
