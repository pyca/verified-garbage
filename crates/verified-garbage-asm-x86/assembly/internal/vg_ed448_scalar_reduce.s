// The functions of `src/internal/vg_ed448_scalar_reduce.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
