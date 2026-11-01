// The functions of `src/camellia_cbc.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_cbc_encrypt_chained:
	lea esp, [esp-2756]
	mov eax, DWORD PTR [esp+2760]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2764]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2768]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2772]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2776]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2688], ebx
	mov DWORD PTR [eax+2692], esi
	mov DWORD PTR [eax+2696], edi
	mov DWORD PTR [eax+2700], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [esp+8]
	cmp eax, 18
	je 20f
	mov ecx, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 416
	mov ebp, 34
22:
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+4], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+8], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+12], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+16], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+20], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+24], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+28], ebx
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+32], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+36], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+40], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+44], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+48], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+52], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+56], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+60], ebx
	add esi, 64
	add ecx, 8
	sub ebp, 1
	jne 22b
	jmp 21f
20:
	mov ecx, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 416
	mov ebp, 26
23:
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+4], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+8], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+12], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+16], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+20], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+24], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+28], ebx
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+32], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+36], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+40], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+44], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+48], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+52], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+56], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+60], ebx
	add esi, 64
	add ecx, 8
	sub ebp, 1
	jne 23b
21:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+2704], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+2708], eax
	test eax, eax
	je 24f
26:
	mov esi, DWORD PTR [edi+2704]
	mov ebp, DWORD PTR [edi+2708]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, edi
	mov edx, 336
	push edx
	push ecx
	push eax
	call {vg_camellia_crypt_prepared}
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [edi+2704]
	mov ebp, DWORD PTR [edi+2708]
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+2704], esi
	mov DWORD PTR [edi+2708], ebp
	jne 26b
	jmp 25f
24:
25:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+2688]
	mov esi, DWORD PTR [edi+2692]
	mov ebp, DWORD PTR [edi+2700]
	mov edi, DWORD PTR [edi+2696]
	mov ecx, 0
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
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov DWORD PTR [esp+468], ecx
	mov DWORD PTR [esp+472], ecx
	mov DWORD PTR [esp+476], ecx
	mov DWORD PTR [esp+480], ecx
	mov DWORD PTR [esp+484], ecx
	mov DWORD PTR [esp+488], ecx
	mov DWORD PTR [esp+492], ecx
	mov DWORD PTR [esp+496], ecx
	mov DWORD PTR [esp+500], ecx
	mov DWORD PTR [esp+504], ecx
	mov DWORD PTR [esp+508], ecx
	mov DWORD PTR [esp+512], ecx
	mov DWORD PTR [esp+516], ecx
	mov DWORD PTR [esp+520], ecx
	mov DWORD PTR [esp+524], ecx
	mov DWORD PTR [esp+528], ecx
	mov DWORD PTR [esp+532], ecx
	mov DWORD PTR [esp+536], ecx
	mov DWORD PTR [esp+540], ecx
	mov DWORD PTR [esp+544], ecx
	mov DWORD PTR [esp+548], ecx
	mov DWORD PTR [esp+552], ecx
	mov DWORD PTR [esp+556], ecx
	mov DWORD PTR [esp+560], ecx
	mov DWORD PTR [esp+564], ecx
	mov DWORD PTR [esp+568], ecx
	mov DWORD PTR [esp+572], ecx
	mov DWORD PTR [esp+576], ecx
	mov DWORD PTR [esp+580], ecx
	mov DWORD PTR [esp+584], ecx
	mov DWORD PTR [esp+588], ecx
	mov DWORD PTR [esp+592], ecx
	mov DWORD PTR [esp+596], ecx
	mov DWORD PTR [esp+600], ecx
	mov DWORD PTR [esp+604], ecx
	mov DWORD PTR [esp+608], ecx
	mov DWORD PTR [esp+612], ecx
	mov DWORD PTR [esp+616], ecx
	mov DWORD PTR [esp+620], ecx
	mov DWORD PTR [esp+624], ecx
	mov DWORD PTR [esp+628], ecx
	mov DWORD PTR [esp+632], ecx
	mov DWORD PTR [esp+636], ecx
	mov DWORD PTR [esp+640], ecx
	mov DWORD PTR [esp+644], ecx
	mov DWORD PTR [esp+648], ecx
	mov DWORD PTR [esp+652], ecx
	mov DWORD PTR [esp+656], ecx
	mov DWORD PTR [esp+660], ecx
	mov DWORD PTR [esp+664], ecx
	mov DWORD PTR [esp+668], ecx
	mov DWORD PTR [esp+672], ecx
	mov DWORD PTR [esp+676], ecx
	mov DWORD PTR [esp+680], ecx
	mov DWORD PTR [esp+684], ecx
	mov DWORD PTR [esp+688], ecx
	mov DWORD PTR [esp+692], ecx
	mov DWORD PTR [esp+696], ecx
	mov DWORD PTR [esp+700], ecx
	mov DWORD PTR [esp+704], ecx
	mov DWORD PTR [esp+708], ecx
	mov DWORD PTR [esp+712], ecx
	mov DWORD PTR [esp+716], ecx
	mov DWORD PTR [esp+720], ecx
	mov DWORD PTR [esp+724], ecx
	mov DWORD PTR [esp+728], ecx
	mov DWORD PTR [esp+732], ecx
	mov DWORD PTR [esp+736], ecx
	mov DWORD PTR [esp+740], ecx
	mov DWORD PTR [esp+744], ecx
	mov DWORD PTR [esp+748], ecx
	mov DWORD PTR [esp+752], ecx
	mov DWORD PTR [esp+756], ecx
	mov DWORD PTR [esp+760], ecx
	mov DWORD PTR [esp+764], ecx
	mov DWORD PTR [esp+768], ecx
	mov DWORD PTR [esp+772], ecx
	mov DWORD PTR [esp+776], ecx
	mov DWORD PTR [esp+780], ecx
	mov DWORD PTR [esp+784], ecx
	mov DWORD PTR [esp+788], ecx
	mov DWORD PTR [esp+792], ecx
	mov DWORD PTR [esp+796], ecx
	mov DWORD PTR [esp+800], ecx
	mov DWORD PTR [esp+804], ecx
	mov DWORD PTR [esp+808], ecx
	mov DWORD PTR [esp+812], ecx
	mov DWORD PTR [esp+816], ecx
	mov DWORD PTR [esp+820], ecx
	mov DWORD PTR [esp+824], ecx
	mov DWORD PTR [esp+828], ecx
	mov DWORD PTR [esp+832], ecx
	mov DWORD PTR [esp+836], ecx
	mov DWORD PTR [esp+840], ecx
	mov DWORD PTR [esp+844], ecx
	mov DWORD PTR [esp+848], ecx
	mov DWORD PTR [esp+852], ecx
	mov DWORD PTR [esp+856], ecx
	mov DWORD PTR [esp+860], ecx
	mov DWORD PTR [esp+864], ecx
	mov DWORD PTR [esp+868], ecx
	mov DWORD PTR [esp+872], ecx
	mov DWORD PTR [esp+876], ecx
	mov DWORD PTR [esp+880], ecx
	mov DWORD PTR [esp+884], ecx
	mov DWORD PTR [esp+888], ecx
	mov DWORD PTR [esp+892], ecx
	mov DWORD PTR [esp+896], ecx
	mov DWORD PTR [esp+900], ecx
	mov DWORD PTR [esp+904], ecx
	mov DWORD PTR [esp+908], ecx
	mov DWORD PTR [esp+912], ecx
	mov DWORD PTR [esp+916], ecx
	mov DWORD PTR [esp+920], ecx
	mov DWORD PTR [esp+924], ecx
	mov DWORD PTR [esp+928], ecx
	mov DWORD PTR [esp+932], ecx
	mov DWORD PTR [esp+936], ecx
	mov DWORD PTR [esp+940], ecx
	mov DWORD PTR [esp+944], ecx
	mov DWORD PTR [esp+948], ecx
	mov DWORD PTR [esp+952], ecx
	mov DWORD PTR [esp+956], ecx
	mov DWORD PTR [esp+960], ecx
	mov DWORD PTR [esp+964], ecx
	mov DWORD PTR [esp+968], ecx
	mov DWORD PTR [esp+972], ecx
	mov DWORD PTR [esp+976], ecx
	mov DWORD PTR [esp+980], ecx
	mov DWORD PTR [esp+984], ecx
	mov DWORD PTR [esp+988], ecx
	mov DWORD PTR [esp+992], ecx
	mov DWORD PTR [esp+996], ecx
	mov DWORD PTR [esp+1000], ecx
	mov DWORD PTR [esp+1004], ecx
	mov DWORD PTR [esp+1008], ecx
	mov DWORD PTR [esp+1012], ecx
	mov DWORD PTR [esp+1016], ecx
	mov DWORD PTR [esp+1020], ecx
	mov DWORD PTR [esp+1024], ecx
	mov DWORD PTR [esp+1028], ecx
	mov DWORD PTR [esp+1032], ecx
	mov DWORD PTR [esp+1036], ecx
	mov DWORD PTR [esp+1040], ecx
	mov DWORD PTR [esp+1044], ecx
	mov DWORD PTR [esp+1048], ecx
	mov DWORD PTR [esp+1052], ecx
	mov DWORD PTR [esp+1056], ecx
	mov DWORD PTR [esp+1060], ecx
	mov DWORD PTR [esp+1064], ecx
	mov DWORD PTR [esp+1068], ecx
	mov DWORD PTR [esp+1072], ecx
	mov DWORD PTR [esp+1076], ecx
	mov DWORD PTR [esp+1080], ecx
	mov DWORD PTR [esp+1084], ecx
	mov DWORD PTR [esp+1088], ecx
	mov DWORD PTR [esp+1092], ecx
	mov DWORD PTR [esp+1096], ecx
	mov DWORD PTR [esp+1100], ecx
	mov DWORD PTR [esp+1104], ecx
	mov DWORD PTR [esp+1108], ecx
	mov DWORD PTR [esp+1112], ecx
	mov DWORD PTR [esp+1116], ecx
	mov DWORD PTR [esp+1120], ecx
	mov DWORD PTR [esp+1124], ecx
	mov DWORD PTR [esp+1128], ecx
	mov DWORD PTR [esp+1132], ecx
	mov DWORD PTR [esp+1136], ecx
	mov DWORD PTR [esp+1140], ecx
	mov DWORD PTR [esp+1144], ecx
	mov DWORD PTR [esp+1148], ecx
	mov DWORD PTR [esp+1152], ecx
	mov DWORD PTR [esp+1156], ecx
	mov DWORD PTR [esp+1160], ecx
	mov DWORD PTR [esp+1164], ecx
	mov DWORD PTR [esp+1168], ecx
	mov DWORD PTR [esp+1172], ecx
	mov DWORD PTR [esp+1176], ecx
	mov DWORD PTR [esp+1180], ecx
	mov DWORD PTR [esp+1184], ecx
	mov DWORD PTR [esp+1188], ecx
	mov DWORD PTR [esp+1192], ecx
	mov DWORD PTR [esp+1196], ecx
	mov DWORD PTR [esp+1200], ecx
	mov DWORD PTR [esp+1204], ecx
	mov DWORD PTR [esp+1208], ecx
	mov DWORD PTR [esp+1212], ecx
	mov DWORD PTR [esp+1216], ecx
	mov DWORD PTR [esp+1220], ecx
	mov DWORD PTR [esp+1224], ecx
	mov DWORD PTR [esp+1228], ecx
	mov DWORD PTR [esp+1232], ecx
	mov DWORD PTR [esp+1236], ecx
	mov DWORD PTR [esp+1240], ecx
	mov DWORD PTR [esp+1244], ecx
	mov DWORD PTR [esp+1248], ecx
	mov DWORD PTR [esp+1252], ecx
	mov DWORD PTR [esp+1256], ecx
	mov DWORD PTR [esp+1260], ecx
	mov DWORD PTR [esp+1264], ecx
	mov DWORD PTR [esp+1268], ecx
	mov DWORD PTR [esp+1272], ecx
	mov DWORD PTR [esp+1276], ecx
	mov DWORD PTR [esp+1280], ecx
	mov DWORD PTR [esp+1284], ecx
	mov DWORD PTR [esp+1288], ecx
	mov DWORD PTR [esp+1292], ecx
	mov DWORD PTR [esp+1296], ecx
	mov DWORD PTR [esp+1300], ecx
	mov DWORD PTR [esp+1304], ecx
	mov DWORD PTR [esp+1308], ecx
	mov DWORD PTR [esp+1312], ecx
	mov DWORD PTR [esp+1316], ecx
	mov DWORD PTR [esp+1320], ecx
	mov DWORD PTR [esp+1324], ecx
	mov DWORD PTR [esp+1328], ecx
	mov DWORD PTR [esp+1332], ecx
	mov DWORD PTR [esp+1336], ecx
	mov DWORD PTR [esp+1340], ecx
	mov DWORD PTR [esp+1344], ecx
	mov DWORD PTR [esp+1348], ecx
	mov DWORD PTR [esp+1352], ecx
	mov DWORD PTR [esp+1356], ecx
	mov DWORD PTR [esp+1360], ecx
	mov DWORD PTR [esp+1364], ecx
	mov DWORD PTR [esp+1368], ecx
	mov DWORD PTR [esp+1372], ecx
	mov DWORD PTR [esp+1376], ecx
	mov DWORD PTR [esp+1380], ecx
	mov DWORD PTR [esp+1384], ecx
	mov DWORD PTR [esp+1388], ecx
	mov DWORD PTR [esp+1392], ecx
	mov DWORD PTR [esp+1396], ecx
	mov DWORD PTR [esp+1400], ecx
	mov DWORD PTR [esp+1404], ecx
	mov DWORD PTR [esp+1408], ecx
	mov DWORD PTR [esp+1412], ecx
	mov DWORD PTR [esp+1416], ecx
	mov DWORD PTR [esp+1420], ecx
	mov DWORD PTR [esp+1424], ecx
	mov DWORD PTR [esp+1428], ecx
	mov DWORD PTR [esp+1432], ecx
	mov DWORD PTR [esp+1436], ecx
	mov DWORD PTR [esp+1440], ecx
	mov DWORD PTR [esp+1444], ecx
	mov DWORD PTR [esp+1448], ecx
	mov DWORD PTR [esp+1452], ecx
	mov DWORD PTR [esp+1456], ecx
	mov DWORD PTR [esp+1460], ecx
	mov DWORD PTR [esp+1464], ecx
	mov DWORD PTR [esp+1468], ecx
	mov DWORD PTR [esp+1472], ecx
	mov DWORD PTR [esp+1476], ecx
	mov DWORD PTR [esp+1480], ecx
	mov DWORD PTR [esp+1484], ecx
	mov DWORD PTR [esp+1488], ecx
	mov DWORD PTR [esp+1492], ecx
	mov DWORD PTR [esp+1496], ecx
	mov DWORD PTR [esp+1500], ecx
	mov DWORD PTR [esp+1504], ecx
	mov DWORD PTR [esp+1508], ecx
	mov DWORD PTR [esp+1512], ecx
	mov DWORD PTR [esp+1516], ecx
	mov DWORD PTR [esp+1520], ecx
	mov DWORD PTR [esp+1524], ecx
	mov DWORD PTR [esp+1528], ecx
	mov DWORD PTR [esp+1532], ecx
	mov DWORD PTR [esp+1536], ecx
	mov DWORD PTR [esp+1540], ecx
	mov DWORD PTR [esp+1544], ecx
	mov DWORD PTR [esp+1548], ecx
	mov DWORD PTR [esp+1552], ecx
	mov DWORD PTR [esp+1556], ecx
	mov DWORD PTR [esp+1560], ecx
	mov DWORD PTR [esp+1564], ecx
	mov DWORD PTR [esp+1568], ecx
	mov DWORD PTR [esp+1572], ecx
	mov DWORD PTR [esp+1576], ecx
	mov DWORD PTR [esp+1580], ecx
	mov DWORD PTR [esp+1584], ecx
	mov DWORD PTR [esp+1588], ecx
	mov DWORD PTR [esp+1592], ecx
	mov DWORD PTR [esp+1596], ecx
	mov DWORD PTR [esp+1600], ecx
	mov DWORD PTR [esp+1604], ecx
	mov DWORD PTR [esp+1608], ecx
	mov DWORD PTR [esp+1612], ecx
	mov DWORD PTR [esp+1616], ecx
	mov DWORD PTR [esp+1620], ecx
	mov DWORD PTR [esp+1624], ecx
	mov DWORD PTR [esp+1628], ecx
	mov DWORD PTR [esp+1632], ecx
	mov DWORD PTR [esp+1636], ecx
	mov DWORD PTR [esp+1640], ecx
	mov DWORD PTR [esp+1644], ecx
	mov DWORD PTR [esp+1648], ecx
	mov DWORD PTR [esp+1652], ecx
	mov DWORD PTR [esp+1656], ecx
	mov DWORD PTR [esp+1660], ecx
	mov DWORD PTR [esp+1664], ecx
	mov DWORD PTR [esp+1668], ecx
	mov DWORD PTR [esp+1672], ecx
	mov DWORD PTR [esp+1676], ecx
	mov DWORD PTR [esp+1680], ecx
	mov DWORD PTR [esp+1684], ecx
	mov DWORD PTR [esp+1688], ecx
	mov DWORD PTR [esp+1692], ecx
	mov DWORD PTR [esp+1696], ecx
	mov DWORD PTR [esp+1700], ecx
	mov DWORD PTR [esp+1704], ecx
	mov DWORD PTR [esp+1708], ecx
	mov DWORD PTR [esp+1712], ecx
	mov DWORD PTR [esp+1716], ecx
	mov DWORD PTR [esp+1720], ecx
	mov DWORD PTR [esp+1724], ecx
	mov DWORD PTR [esp+1728], ecx
	mov DWORD PTR [esp+1732], ecx
	mov DWORD PTR [esp+1736], ecx
	mov DWORD PTR [esp+1740], ecx
	mov DWORD PTR [esp+1744], ecx
	mov DWORD PTR [esp+1748], ecx
	mov DWORD PTR [esp+1752], ecx
	mov DWORD PTR [esp+1756], ecx
	mov DWORD PTR [esp+1760], ecx
	mov DWORD PTR [esp+1764], ecx
	mov DWORD PTR [esp+1768], ecx
	mov DWORD PTR [esp+1772], ecx
	mov DWORD PTR [esp+1776], ecx
	mov DWORD PTR [esp+1780], ecx
	mov DWORD PTR [esp+1784], ecx
	mov DWORD PTR [esp+1788], ecx
	mov DWORD PTR [esp+1792], ecx
	mov DWORD PTR [esp+1796], ecx
	mov DWORD PTR [esp+1800], ecx
	mov DWORD PTR [esp+1804], ecx
	mov DWORD PTR [esp+1808], ecx
	mov DWORD PTR [esp+1812], ecx
	mov DWORD PTR [esp+1816], ecx
	mov DWORD PTR [esp+1820], ecx
	mov DWORD PTR [esp+1824], ecx
	mov DWORD PTR [esp+1828], ecx
	mov DWORD PTR [esp+1832], ecx
	mov DWORD PTR [esp+1836], ecx
	mov DWORD PTR [esp+1840], ecx
	mov DWORD PTR [esp+1844], ecx
	mov DWORD PTR [esp+1848], ecx
	mov DWORD PTR [esp+1852], ecx
	mov DWORD PTR [esp+1856], ecx
	mov DWORD PTR [esp+1860], ecx
	mov DWORD PTR [esp+1864], ecx
	mov DWORD PTR [esp+1868], ecx
	mov DWORD PTR [esp+1872], ecx
	mov DWORD PTR [esp+1876], ecx
	mov DWORD PTR [esp+1880], ecx
	mov DWORD PTR [esp+1884], ecx
	mov DWORD PTR [esp+1888], ecx
	mov DWORD PTR [esp+1892], ecx
	mov DWORD PTR [esp+1896], ecx
	mov DWORD PTR [esp+1900], ecx
	mov DWORD PTR [esp+1904], ecx
	mov DWORD PTR [esp+1908], ecx
	mov DWORD PTR [esp+1912], ecx
	mov DWORD PTR [esp+1916], ecx
	mov DWORD PTR [esp+1920], ecx
	mov DWORD PTR [esp+1924], ecx
	mov DWORD PTR [esp+1928], ecx
	mov DWORD PTR [esp+1932], ecx
	mov DWORD PTR [esp+1936], ecx
	mov DWORD PTR [esp+1940], ecx
	mov DWORD PTR [esp+1944], ecx
	mov DWORD PTR [esp+1948], ecx
	mov DWORD PTR [esp+1952], ecx
	mov DWORD PTR [esp+1956], ecx
	mov DWORD PTR [esp+1960], ecx
	mov DWORD PTR [esp+1964], ecx
	mov DWORD PTR [esp+1968], ecx
	mov DWORD PTR [esp+1972], ecx
	mov DWORD PTR [esp+1976], ecx
	mov DWORD PTR [esp+1980], ecx
	mov DWORD PTR [esp+1984], ecx
	mov DWORD PTR [esp+1988], ecx
	mov DWORD PTR [esp+1992], ecx
	mov DWORD PTR [esp+1996], ecx
	mov DWORD PTR [esp+2000], ecx
	mov DWORD PTR [esp+2004], ecx
	mov DWORD PTR [esp+2008], ecx
	mov DWORD PTR [esp+2012], ecx
	mov DWORD PTR [esp+2016], ecx
	mov DWORD PTR [esp+2020], ecx
	mov DWORD PTR [esp+2024], ecx
	mov DWORD PTR [esp+2028], ecx
	mov DWORD PTR [esp+2032], ecx
	mov DWORD PTR [esp+2036], ecx
	mov DWORD PTR [esp+2040], ecx
	mov DWORD PTR [esp+2044], ecx
	mov DWORD PTR [esp+2048], ecx
	mov DWORD PTR [esp+2052], ecx
	mov DWORD PTR [esp+2056], ecx
	mov DWORD PTR [esp+2060], ecx
	mov DWORD PTR [esp+2064], ecx
	mov DWORD PTR [esp+2068], ecx
	mov DWORD PTR [esp+2072], ecx
	mov DWORD PTR [esp+2076], ecx
	mov DWORD PTR [esp+2080], ecx
	mov DWORD PTR [esp+2084], ecx
	mov DWORD PTR [esp+2088], ecx
	mov DWORD PTR [esp+2092], ecx
	mov DWORD PTR [esp+2096], ecx
	mov DWORD PTR [esp+2100], ecx
	mov DWORD PTR [esp+2104], ecx
	mov DWORD PTR [esp+2108], ecx
	mov DWORD PTR [esp+2112], ecx
	mov DWORD PTR [esp+2116], ecx
	mov DWORD PTR [esp+2120], ecx
	mov DWORD PTR [esp+2124], ecx
	mov DWORD PTR [esp+2128], ecx
	mov DWORD PTR [esp+2132], ecx
	mov DWORD PTR [esp+2136], ecx
	mov DWORD PTR [esp+2140], ecx
	mov DWORD PTR [esp+2144], ecx
	mov DWORD PTR [esp+2148], ecx
	mov DWORD PTR [esp+2152], ecx
	mov DWORD PTR [esp+2156], ecx
	mov DWORD PTR [esp+2160], ecx
	mov DWORD PTR [esp+2164], ecx
	mov DWORD PTR [esp+2168], ecx
	mov DWORD PTR [esp+2172], ecx
	mov DWORD PTR [esp+2176], ecx
	mov DWORD PTR [esp+2180], ecx
	mov DWORD PTR [esp+2184], ecx
	mov DWORD PTR [esp+2188], ecx
	mov DWORD PTR [esp+2192], ecx
	mov DWORD PTR [esp+2196], ecx
	mov DWORD PTR [esp+2200], ecx
	mov DWORD PTR [esp+2204], ecx
	mov DWORD PTR [esp+2208], ecx
	mov DWORD PTR [esp+2212], ecx
	mov DWORD PTR [esp+2216], ecx
	mov DWORD PTR [esp+2220], ecx
	mov DWORD PTR [esp+2224], ecx
	mov DWORD PTR [esp+2228], ecx
	mov DWORD PTR [esp+2232], ecx
	mov DWORD PTR [esp+2236], ecx
	mov DWORD PTR [esp+2240], ecx
	mov DWORD PTR [esp+2244], ecx
	mov DWORD PTR [esp+2248], ecx
	mov DWORD PTR [esp+2252], ecx
	mov DWORD PTR [esp+2256], ecx
	mov DWORD PTR [esp+2260], ecx
	mov DWORD PTR [esp+2264], ecx
	mov DWORD PTR [esp+2268], ecx
	mov DWORD PTR [esp+2272], ecx
	mov DWORD PTR [esp+2276], ecx
	mov DWORD PTR [esp+2280], ecx
	mov DWORD PTR [esp+2284], ecx
	mov DWORD PTR [esp+2288], ecx
	mov DWORD PTR [esp+2292], ecx
	mov DWORD PTR [esp+2296], ecx
	mov DWORD PTR [esp+2300], ecx
	mov DWORD PTR [esp+2304], ecx
	mov DWORD PTR [esp+2308], ecx
	mov DWORD PTR [esp+2312], ecx
	mov DWORD PTR [esp+2316], ecx
	mov DWORD PTR [esp+2320], ecx
	mov DWORD PTR [esp+2324], ecx
	mov DWORD PTR [esp+2328], ecx
	mov DWORD PTR [esp+2332], ecx
	mov DWORD PTR [esp+2336], ecx
	mov DWORD PTR [esp+2340], ecx
	mov DWORD PTR [esp+2344], ecx
	mov DWORD PTR [esp+2348], ecx
	mov DWORD PTR [esp+2352], ecx
	mov DWORD PTR [esp+2356], ecx
	mov DWORD PTR [esp+2360], ecx
	mov DWORD PTR [esp+2364], ecx
	mov DWORD PTR [esp+2368], ecx
	mov DWORD PTR [esp+2372], ecx
	mov DWORD PTR [esp+2376], ecx
	mov DWORD PTR [esp+2380], ecx
	mov DWORD PTR [esp+2384], ecx
	mov DWORD PTR [esp+2388], ecx
	mov DWORD PTR [esp+2392], ecx
	mov DWORD PTR [esp+2396], ecx
	mov DWORD PTR [esp+2400], ecx
	mov DWORD PTR [esp+2404], ecx
	mov DWORD PTR [esp+2408], ecx
	mov DWORD PTR [esp+2412], ecx
	mov DWORD PTR [esp+2416], ecx
	mov DWORD PTR [esp+2420], ecx
	mov DWORD PTR [esp+2424], ecx
	mov DWORD PTR [esp+2428], ecx
	mov DWORD PTR [esp+2432], ecx
	mov DWORD PTR [esp+2436], ecx
	mov DWORD PTR [esp+2440], ecx
	mov DWORD PTR [esp+2444], ecx
	mov DWORD PTR [esp+2448], ecx
	mov DWORD PTR [esp+2452], ecx
	mov DWORD PTR [esp+2456], ecx
	mov DWORD PTR [esp+2460], ecx
	mov DWORD PTR [esp+2464], ecx
	mov DWORD PTR [esp+2468], ecx
	mov DWORD PTR [esp+2472], ecx
	mov DWORD PTR [esp+2476], ecx
	mov DWORD PTR [esp+2480], ecx
	mov DWORD PTR [esp+2484], ecx
	mov DWORD PTR [esp+2488], ecx
	mov DWORD PTR [esp+2492], ecx
	mov DWORD PTR [esp+2496], ecx
	mov DWORD PTR [esp+2500], ecx
	mov DWORD PTR [esp+2504], ecx
	mov DWORD PTR [esp+2508], ecx
	mov DWORD PTR [esp+2512], ecx
	mov DWORD PTR [esp+2516], ecx
	mov DWORD PTR [esp+2520], ecx
	mov DWORD PTR [esp+2524], ecx
	mov DWORD PTR [esp+2528], ecx
	mov DWORD PTR [esp+2532], ecx
	mov DWORD PTR [esp+2536], ecx
	mov DWORD PTR [esp+2540], ecx
	mov DWORD PTR [esp+2544], ecx
	mov DWORD PTR [esp+2548], ecx
	mov DWORD PTR [esp+2552], ecx
	mov DWORD PTR [esp+2556], ecx
	mov DWORD PTR [esp+2560], ecx
	mov DWORD PTR [esp+2564], ecx
	mov DWORD PTR [esp+2568], ecx
	mov DWORD PTR [esp+2572], ecx
	mov DWORD PTR [esp+2576], ecx
	mov DWORD PTR [esp+2580], ecx
	mov DWORD PTR [esp+2584], ecx
	mov DWORD PTR [esp+2588], ecx
	mov DWORD PTR [esp+2592], ecx
	mov DWORD PTR [esp+2596], ecx
	mov DWORD PTR [esp+2600], ecx
	mov DWORD PTR [esp+2604], ecx
	mov DWORD PTR [esp+2608], ecx
	mov DWORD PTR [esp+2612], ecx
	mov DWORD PTR [esp+2616], ecx
	mov DWORD PTR [esp+2620], ecx
	mov DWORD PTR [esp+2624], ecx
	mov DWORD PTR [esp+2628], ecx
	mov DWORD PTR [esp+2632], ecx
	mov DWORD PTR [esp+2636], ecx
	mov DWORD PTR [esp+2640], ecx
	mov DWORD PTR [esp+2644], ecx
	mov DWORD PTR [esp+2648], ecx
	mov DWORD PTR [esp+2652], ecx
	mov DWORD PTR [esp+2656], ecx
	mov DWORD PTR [esp+2660], ecx
	mov DWORD PTR [esp+2664], ecx
	mov DWORD PTR [esp+2668], ecx
	mov DWORD PTR [esp+2672], ecx
	mov DWORD PTR [esp+2676], ecx
	mov DWORD PTR [esp+2680], ecx
	mov DWORD PTR [esp+2684], ecx
	mov DWORD PTR [esp+2688], ecx
	mov DWORD PTR [esp+2692], ecx
	mov DWORD PTR [esp+2696], ecx
	mov DWORD PTR [esp+2700], ecx
	mov DWORD PTR [esp+2704], ecx
	mov DWORD PTR [esp+2708], ecx
	mov DWORD PTR [esp+2712], ecx
	mov DWORD PTR [esp+2716], ecx
	mov DWORD PTR [esp+2720], ecx
	mov DWORD PTR [esp+2724], ecx
	mov DWORD PTR [esp+2728], ecx
	mov DWORD PTR [esp+2732], ecx
	mov DWORD PTR [esp+2736], ecx
	mov DWORD PTR [esp+2740], ecx
	mov DWORD PTR [esp+2744], ecx
	mov DWORD PTR [esp+2748], ecx
	mov DWORD PTR [esp+2752], ecx
	lea esp, [esp+2756]
	ret
	.p2align 6

vg_camellia_cbc_decrypt_chained:
	lea esp, [esp-2756]
	mov eax, DWORD PTR [esp+2760]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2764]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2768]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2772]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2776]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2688], ebx
	mov DWORD PTR [eax+2692], esi
	mov DWORD PTR [eax+2696], edi
	mov DWORD PTR [eax+2700], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [esp+8]
	cmp eax, 18
	je 20f
	mov ecx, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 416
	add ecx, 256
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+4], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+8], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+12], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+16], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+20], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+24], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+28], ebx
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+32], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+36], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+40], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+44], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+48], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+52], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+56], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+60], ebx
	add esi, 64
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+4], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+8], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+12], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+16], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+20], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+24], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+28], ebx
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+32], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+36], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+40], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+44], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+48], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+52], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+56], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+60], ebx
	add esi, 64
	sub ecx, 8
	mov ebp, 30
22:
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+4], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+8], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+12], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+16], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+20], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+24], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+28], ebx
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+32], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+36], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+40], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+44], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+48], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+52], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+56], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+60], ebx
	add esi, 64
	sub ecx, 8
	sub ebp, 1
	jne 22b
	sub ecx, 8
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+4], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+8], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+12], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+16], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+20], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+24], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+28], ebx
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+32], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+36], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+40], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+44], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+48], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+52], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+56], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+60], ebx
	add esi, 64
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+4], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+8], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+12], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+16], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+20], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+24], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+28], ebx
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+32], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+36], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+40], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+44], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+48], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+52], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+56], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+60], ebx
	add esi, 64
	jmp 21f
20:
	mov ecx, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 416
	add ecx, 192
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+4], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+8], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+12], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+16], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+20], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+24], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+28], ebx
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+32], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+36], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+40], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+44], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+48], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+52], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+56], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+60], ebx
	add esi, 64
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+4], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+8], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+12], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+16], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+20], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+24], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+28], ebx
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+32], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+36], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+40], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+44], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+48], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+52], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+56], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+60], ebx
	add esi, 64
	sub ecx, 8
	mov ebp, 22
23:
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+4], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+8], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+12], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+16], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+20], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+24], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+28], ebx
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+32], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+36], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+40], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+44], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+48], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+52], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+56], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+60], ebx
	add esi, 64
	sub ecx, 8
	sub ebp, 1
	jne 23b
	sub ecx, 8
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+4], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+8], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+12], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+16], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+20], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+24], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+28], ebx
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+32], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+36], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+40], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+44], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+48], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+52], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+56], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+60], ebx
	add esi, 64
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+4], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+8], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+12], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+16], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+20], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+24], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+28], ebx
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+32], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+36], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+40], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+44], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+48], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+52], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+56], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+60], ebx
	add esi, 64
21:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+2704], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+2708], eax
	test eax, eax
	je 24f
26:
	mov esi, DWORD PTR [edi+2704]
	mov ebp, DWORD PTR [edi+2708]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, edi
	mov edx, 336
	push edx
	push ecx
	push eax
	call {vg_camellia_crypt_prepared}
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [edi+2704]
	mov ebp, DWORD PTR [edi+2708]
	mov eax, DWORD PTR [edi+288]
	xor eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	xor eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	xor eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	xor eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+2704], esi
	mov DWORD PTR [edi+2708], ebp
	jne 26b
	jmp 25f
24:
25:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+2688]
	mov esi, DWORD PTR [edi+2692]
	mov ebp, DWORD PTR [edi+2700]
	mov edi, DWORD PTR [edi+2696]
	mov ecx, 0
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
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov DWORD PTR [esp+468], ecx
	mov DWORD PTR [esp+472], ecx
	mov DWORD PTR [esp+476], ecx
	mov DWORD PTR [esp+480], ecx
	mov DWORD PTR [esp+484], ecx
	mov DWORD PTR [esp+488], ecx
	mov DWORD PTR [esp+492], ecx
	mov DWORD PTR [esp+496], ecx
	mov DWORD PTR [esp+500], ecx
	mov DWORD PTR [esp+504], ecx
	mov DWORD PTR [esp+508], ecx
	mov DWORD PTR [esp+512], ecx
	mov DWORD PTR [esp+516], ecx
	mov DWORD PTR [esp+520], ecx
	mov DWORD PTR [esp+524], ecx
	mov DWORD PTR [esp+528], ecx
	mov DWORD PTR [esp+532], ecx
	mov DWORD PTR [esp+536], ecx
	mov DWORD PTR [esp+540], ecx
	mov DWORD PTR [esp+544], ecx
	mov DWORD PTR [esp+548], ecx
	mov DWORD PTR [esp+552], ecx
	mov DWORD PTR [esp+556], ecx
	mov DWORD PTR [esp+560], ecx
	mov DWORD PTR [esp+564], ecx
	mov DWORD PTR [esp+568], ecx
	mov DWORD PTR [esp+572], ecx
	mov DWORD PTR [esp+576], ecx
	mov DWORD PTR [esp+580], ecx
	mov DWORD PTR [esp+584], ecx
	mov DWORD PTR [esp+588], ecx
	mov DWORD PTR [esp+592], ecx
	mov DWORD PTR [esp+596], ecx
	mov DWORD PTR [esp+600], ecx
	mov DWORD PTR [esp+604], ecx
	mov DWORD PTR [esp+608], ecx
	mov DWORD PTR [esp+612], ecx
	mov DWORD PTR [esp+616], ecx
	mov DWORD PTR [esp+620], ecx
	mov DWORD PTR [esp+624], ecx
	mov DWORD PTR [esp+628], ecx
	mov DWORD PTR [esp+632], ecx
	mov DWORD PTR [esp+636], ecx
	mov DWORD PTR [esp+640], ecx
	mov DWORD PTR [esp+644], ecx
	mov DWORD PTR [esp+648], ecx
	mov DWORD PTR [esp+652], ecx
	mov DWORD PTR [esp+656], ecx
	mov DWORD PTR [esp+660], ecx
	mov DWORD PTR [esp+664], ecx
	mov DWORD PTR [esp+668], ecx
	mov DWORD PTR [esp+672], ecx
	mov DWORD PTR [esp+676], ecx
	mov DWORD PTR [esp+680], ecx
	mov DWORD PTR [esp+684], ecx
	mov DWORD PTR [esp+688], ecx
	mov DWORD PTR [esp+692], ecx
	mov DWORD PTR [esp+696], ecx
	mov DWORD PTR [esp+700], ecx
	mov DWORD PTR [esp+704], ecx
	mov DWORD PTR [esp+708], ecx
	mov DWORD PTR [esp+712], ecx
	mov DWORD PTR [esp+716], ecx
	mov DWORD PTR [esp+720], ecx
	mov DWORD PTR [esp+724], ecx
	mov DWORD PTR [esp+728], ecx
	mov DWORD PTR [esp+732], ecx
	mov DWORD PTR [esp+736], ecx
	mov DWORD PTR [esp+740], ecx
	mov DWORD PTR [esp+744], ecx
	mov DWORD PTR [esp+748], ecx
	mov DWORD PTR [esp+752], ecx
	mov DWORD PTR [esp+756], ecx
	mov DWORD PTR [esp+760], ecx
	mov DWORD PTR [esp+764], ecx
	mov DWORD PTR [esp+768], ecx
	mov DWORD PTR [esp+772], ecx
	mov DWORD PTR [esp+776], ecx
	mov DWORD PTR [esp+780], ecx
	mov DWORD PTR [esp+784], ecx
	mov DWORD PTR [esp+788], ecx
	mov DWORD PTR [esp+792], ecx
	mov DWORD PTR [esp+796], ecx
	mov DWORD PTR [esp+800], ecx
	mov DWORD PTR [esp+804], ecx
	mov DWORD PTR [esp+808], ecx
	mov DWORD PTR [esp+812], ecx
	mov DWORD PTR [esp+816], ecx
	mov DWORD PTR [esp+820], ecx
	mov DWORD PTR [esp+824], ecx
	mov DWORD PTR [esp+828], ecx
	mov DWORD PTR [esp+832], ecx
	mov DWORD PTR [esp+836], ecx
	mov DWORD PTR [esp+840], ecx
	mov DWORD PTR [esp+844], ecx
	mov DWORD PTR [esp+848], ecx
	mov DWORD PTR [esp+852], ecx
	mov DWORD PTR [esp+856], ecx
	mov DWORD PTR [esp+860], ecx
	mov DWORD PTR [esp+864], ecx
	mov DWORD PTR [esp+868], ecx
	mov DWORD PTR [esp+872], ecx
	mov DWORD PTR [esp+876], ecx
	mov DWORD PTR [esp+880], ecx
	mov DWORD PTR [esp+884], ecx
	mov DWORD PTR [esp+888], ecx
	mov DWORD PTR [esp+892], ecx
	mov DWORD PTR [esp+896], ecx
	mov DWORD PTR [esp+900], ecx
	mov DWORD PTR [esp+904], ecx
	mov DWORD PTR [esp+908], ecx
	mov DWORD PTR [esp+912], ecx
	mov DWORD PTR [esp+916], ecx
	mov DWORD PTR [esp+920], ecx
	mov DWORD PTR [esp+924], ecx
	mov DWORD PTR [esp+928], ecx
	mov DWORD PTR [esp+932], ecx
	mov DWORD PTR [esp+936], ecx
	mov DWORD PTR [esp+940], ecx
	mov DWORD PTR [esp+944], ecx
	mov DWORD PTR [esp+948], ecx
	mov DWORD PTR [esp+952], ecx
	mov DWORD PTR [esp+956], ecx
	mov DWORD PTR [esp+960], ecx
	mov DWORD PTR [esp+964], ecx
	mov DWORD PTR [esp+968], ecx
	mov DWORD PTR [esp+972], ecx
	mov DWORD PTR [esp+976], ecx
	mov DWORD PTR [esp+980], ecx
	mov DWORD PTR [esp+984], ecx
	mov DWORD PTR [esp+988], ecx
	mov DWORD PTR [esp+992], ecx
	mov DWORD PTR [esp+996], ecx
	mov DWORD PTR [esp+1000], ecx
	mov DWORD PTR [esp+1004], ecx
	mov DWORD PTR [esp+1008], ecx
	mov DWORD PTR [esp+1012], ecx
	mov DWORD PTR [esp+1016], ecx
	mov DWORD PTR [esp+1020], ecx
	mov DWORD PTR [esp+1024], ecx
	mov DWORD PTR [esp+1028], ecx
	mov DWORD PTR [esp+1032], ecx
	mov DWORD PTR [esp+1036], ecx
	mov DWORD PTR [esp+1040], ecx
	mov DWORD PTR [esp+1044], ecx
	mov DWORD PTR [esp+1048], ecx
	mov DWORD PTR [esp+1052], ecx
	mov DWORD PTR [esp+1056], ecx
	mov DWORD PTR [esp+1060], ecx
	mov DWORD PTR [esp+1064], ecx
	mov DWORD PTR [esp+1068], ecx
	mov DWORD PTR [esp+1072], ecx
	mov DWORD PTR [esp+1076], ecx
	mov DWORD PTR [esp+1080], ecx
	mov DWORD PTR [esp+1084], ecx
	mov DWORD PTR [esp+1088], ecx
	mov DWORD PTR [esp+1092], ecx
	mov DWORD PTR [esp+1096], ecx
	mov DWORD PTR [esp+1100], ecx
	mov DWORD PTR [esp+1104], ecx
	mov DWORD PTR [esp+1108], ecx
	mov DWORD PTR [esp+1112], ecx
	mov DWORD PTR [esp+1116], ecx
	mov DWORD PTR [esp+1120], ecx
	mov DWORD PTR [esp+1124], ecx
	mov DWORD PTR [esp+1128], ecx
	mov DWORD PTR [esp+1132], ecx
	mov DWORD PTR [esp+1136], ecx
	mov DWORD PTR [esp+1140], ecx
	mov DWORD PTR [esp+1144], ecx
	mov DWORD PTR [esp+1148], ecx
	mov DWORD PTR [esp+1152], ecx
	mov DWORD PTR [esp+1156], ecx
	mov DWORD PTR [esp+1160], ecx
	mov DWORD PTR [esp+1164], ecx
	mov DWORD PTR [esp+1168], ecx
	mov DWORD PTR [esp+1172], ecx
	mov DWORD PTR [esp+1176], ecx
	mov DWORD PTR [esp+1180], ecx
	mov DWORD PTR [esp+1184], ecx
	mov DWORD PTR [esp+1188], ecx
	mov DWORD PTR [esp+1192], ecx
	mov DWORD PTR [esp+1196], ecx
	mov DWORD PTR [esp+1200], ecx
	mov DWORD PTR [esp+1204], ecx
	mov DWORD PTR [esp+1208], ecx
	mov DWORD PTR [esp+1212], ecx
	mov DWORD PTR [esp+1216], ecx
	mov DWORD PTR [esp+1220], ecx
	mov DWORD PTR [esp+1224], ecx
	mov DWORD PTR [esp+1228], ecx
	mov DWORD PTR [esp+1232], ecx
	mov DWORD PTR [esp+1236], ecx
	mov DWORD PTR [esp+1240], ecx
	mov DWORD PTR [esp+1244], ecx
	mov DWORD PTR [esp+1248], ecx
	mov DWORD PTR [esp+1252], ecx
	mov DWORD PTR [esp+1256], ecx
	mov DWORD PTR [esp+1260], ecx
	mov DWORD PTR [esp+1264], ecx
	mov DWORD PTR [esp+1268], ecx
	mov DWORD PTR [esp+1272], ecx
	mov DWORD PTR [esp+1276], ecx
	mov DWORD PTR [esp+1280], ecx
	mov DWORD PTR [esp+1284], ecx
	mov DWORD PTR [esp+1288], ecx
	mov DWORD PTR [esp+1292], ecx
	mov DWORD PTR [esp+1296], ecx
	mov DWORD PTR [esp+1300], ecx
	mov DWORD PTR [esp+1304], ecx
	mov DWORD PTR [esp+1308], ecx
	mov DWORD PTR [esp+1312], ecx
	mov DWORD PTR [esp+1316], ecx
	mov DWORD PTR [esp+1320], ecx
	mov DWORD PTR [esp+1324], ecx
	mov DWORD PTR [esp+1328], ecx
	mov DWORD PTR [esp+1332], ecx
	mov DWORD PTR [esp+1336], ecx
	mov DWORD PTR [esp+1340], ecx
	mov DWORD PTR [esp+1344], ecx
	mov DWORD PTR [esp+1348], ecx
	mov DWORD PTR [esp+1352], ecx
	mov DWORD PTR [esp+1356], ecx
	mov DWORD PTR [esp+1360], ecx
	mov DWORD PTR [esp+1364], ecx
	mov DWORD PTR [esp+1368], ecx
	mov DWORD PTR [esp+1372], ecx
	mov DWORD PTR [esp+1376], ecx
	mov DWORD PTR [esp+1380], ecx
	mov DWORD PTR [esp+1384], ecx
	mov DWORD PTR [esp+1388], ecx
	mov DWORD PTR [esp+1392], ecx
	mov DWORD PTR [esp+1396], ecx
	mov DWORD PTR [esp+1400], ecx
	mov DWORD PTR [esp+1404], ecx
	mov DWORD PTR [esp+1408], ecx
	mov DWORD PTR [esp+1412], ecx
	mov DWORD PTR [esp+1416], ecx
	mov DWORD PTR [esp+1420], ecx
	mov DWORD PTR [esp+1424], ecx
	mov DWORD PTR [esp+1428], ecx
	mov DWORD PTR [esp+1432], ecx
	mov DWORD PTR [esp+1436], ecx
	mov DWORD PTR [esp+1440], ecx
	mov DWORD PTR [esp+1444], ecx
	mov DWORD PTR [esp+1448], ecx
	mov DWORD PTR [esp+1452], ecx
	mov DWORD PTR [esp+1456], ecx
	mov DWORD PTR [esp+1460], ecx
	mov DWORD PTR [esp+1464], ecx
	mov DWORD PTR [esp+1468], ecx
	mov DWORD PTR [esp+1472], ecx
	mov DWORD PTR [esp+1476], ecx
	mov DWORD PTR [esp+1480], ecx
	mov DWORD PTR [esp+1484], ecx
	mov DWORD PTR [esp+1488], ecx
	mov DWORD PTR [esp+1492], ecx
	mov DWORD PTR [esp+1496], ecx
	mov DWORD PTR [esp+1500], ecx
	mov DWORD PTR [esp+1504], ecx
	mov DWORD PTR [esp+1508], ecx
	mov DWORD PTR [esp+1512], ecx
	mov DWORD PTR [esp+1516], ecx
	mov DWORD PTR [esp+1520], ecx
	mov DWORD PTR [esp+1524], ecx
	mov DWORD PTR [esp+1528], ecx
	mov DWORD PTR [esp+1532], ecx
	mov DWORD PTR [esp+1536], ecx
	mov DWORD PTR [esp+1540], ecx
	mov DWORD PTR [esp+1544], ecx
	mov DWORD PTR [esp+1548], ecx
	mov DWORD PTR [esp+1552], ecx
	mov DWORD PTR [esp+1556], ecx
	mov DWORD PTR [esp+1560], ecx
	mov DWORD PTR [esp+1564], ecx
	mov DWORD PTR [esp+1568], ecx
	mov DWORD PTR [esp+1572], ecx
	mov DWORD PTR [esp+1576], ecx
	mov DWORD PTR [esp+1580], ecx
	mov DWORD PTR [esp+1584], ecx
	mov DWORD PTR [esp+1588], ecx
	mov DWORD PTR [esp+1592], ecx
	mov DWORD PTR [esp+1596], ecx
	mov DWORD PTR [esp+1600], ecx
	mov DWORD PTR [esp+1604], ecx
	mov DWORD PTR [esp+1608], ecx
	mov DWORD PTR [esp+1612], ecx
	mov DWORD PTR [esp+1616], ecx
	mov DWORD PTR [esp+1620], ecx
	mov DWORD PTR [esp+1624], ecx
	mov DWORD PTR [esp+1628], ecx
	mov DWORD PTR [esp+1632], ecx
	mov DWORD PTR [esp+1636], ecx
	mov DWORD PTR [esp+1640], ecx
	mov DWORD PTR [esp+1644], ecx
	mov DWORD PTR [esp+1648], ecx
	mov DWORD PTR [esp+1652], ecx
	mov DWORD PTR [esp+1656], ecx
	mov DWORD PTR [esp+1660], ecx
	mov DWORD PTR [esp+1664], ecx
	mov DWORD PTR [esp+1668], ecx
	mov DWORD PTR [esp+1672], ecx
	mov DWORD PTR [esp+1676], ecx
	mov DWORD PTR [esp+1680], ecx
	mov DWORD PTR [esp+1684], ecx
	mov DWORD PTR [esp+1688], ecx
	mov DWORD PTR [esp+1692], ecx
	mov DWORD PTR [esp+1696], ecx
	mov DWORD PTR [esp+1700], ecx
	mov DWORD PTR [esp+1704], ecx
	mov DWORD PTR [esp+1708], ecx
	mov DWORD PTR [esp+1712], ecx
	mov DWORD PTR [esp+1716], ecx
	mov DWORD PTR [esp+1720], ecx
	mov DWORD PTR [esp+1724], ecx
	mov DWORD PTR [esp+1728], ecx
	mov DWORD PTR [esp+1732], ecx
	mov DWORD PTR [esp+1736], ecx
	mov DWORD PTR [esp+1740], ecx
	mov DWORD PTR [esp+1744], ecx
	mov DWORD PTR [esp+1748], ecx
	mov DWORD PTR [esp+1752], ecx
	mov DWORD PTR [esp+1756], ecx
	mov DWORD PTR [esp+1760], ecx
	mov DWORD PTR [esp+1764], ecx
	mov DWORD PTR [esp+1768], ecx
	mov DWORD PTR [esp+1772], ecx
	mov DWORD PTR [esp+1776], ecx
	mov DWORD PTR [esp+1780], ecx
	mov DWORD PTR [esp+1784], ecx
	mov DWORD PTR [esp+1788], ecx
	mov DWORD PTR [esp+1792], ecx
	mov DWORD PTR [esp+1796], ecx
	mov DWORD PTR [esp+1800], ecx
	mov DWORD PTR [esp+1804], ecx
	mov DWORD PTR [esp+1808], ecx
	mov DWORD PTR [esp+1812], ecx
	mov DWORD PTR [esp+1816], ecx
	mov DWORD PTR [esp+1820], ecx
	mov DWORD PTR [esp+1824], ecx
	mov DWORD PTR [esp+1828], ecx
	mov DWORD PTR [esp+1832], ecx
	mov DWORD PTR [esp+1836], ecx
	mov DWORD PTR [esp+1840], ecx
	mov DWORD PTR [esp+1844], ecx
	mov DWORD PTR [esp+1848], ecx
	mov DWORD PTR [esp+1852], ecx
	mov DWORD PTR [esp+1856], ecx
	mov DWORD PTR [esp+1860], ecx
	mov DWORD PTR [esp+1864], ecx
	mov DWORD PTR [esp+1868], ecx
	mov DWORD PTR [esp+1872], ecx
	mov DWORD PTR [esp+1876], ecx
	mov DWORD PTR [esp+1880], ecx
	mov DWORD PTR [esp+1884], ecx
	mov DWORD PTR [esp+1888], ecx
	mov DWORD PTR [esp+1892], ecx
	mov DWORD PTR [esp+1896], ecx
	mov DWORD PTR [esp+1900], ecx
	mov DWORD PTR [esp+1904], ecx
	mov DWORD PTR [esp+1908], ecx
	mov DWORD PTR [esp+1912], ecx
	mov DWORD PTR [esp+1916], ecx
	mov DWORD PTR [esp+1920], ecx
	mov DWORD PTR [esp+1924], ecx
	mov DWORD PTR [esp+1928], ecx
	mov DWORD PTR [esp+1932], ecx
	mov DWORD PTR [esp+1936], ecx
	mov DWORD PTR [esp+1940], ecx
	mov DWORD PTR [esp+1944], ecx
	mov DWORD PTR [esp+1948], ecx
	mov DWORD PTR [esp+1952], ecx
	mov DWORD PTR [esp+1956], ecx
	mov DWORD PTR [esp+1960], ecx
	mov DWORD PTR [esp+1964], ecx
	mov DWORD PTR [esp+1968], ecx
	mov DWORD PTR [esp+1972], ecx
	mov DWORD PTR [esp+1976], ecx
	mov DWORD PTR [esp+1980], ecx
	mov DWORD PTR [esp+1984], ecx
	mov DWORD PTR [esp+1988], ecx
	mov DWORD PTR [esp+1992], ecx
	mov DWORD PTR [esp+1996], ecx
	mov DWORD PTR [esp+2000], ecx
	mov DWORD PTR [esp+2004], ecx
	mov DWORD PTR [esp+2008], ecx
	mov DWORD PTR [esp+2012], ecx
	mov DWORD PTR [esp+2016], ecx
	mov DWORD PTR [esp+2020], ecx
	mov DWORD PTR [esp+2024], ecx
	mov DWORD PTR [esp+2028], ecx
	mov DWORD PTR [esp+2032], ecx
	mov DWORD PTR [esp+2036], ecx
	mov DWORD PTR [esp+2040], ecx
	mov DWORD PTR [esp+2044], ecx
	mov DWORD PTR [esp+2048], ecx
	mov DWORD PTR [esp+2052], ecx
	mov DWORD PTR [esp+2056], ecx
	mov DWORD PTR [esp+2060], ecx
	mov DWORD PTR [esp+2064], ecx
	mov DWORD PTR [esp+2068], ecx
	mov DWORD PTR [esp+2072], ecx
	mov DWORD PTR [esp+2076], ecx
	mov DWORD PTR [esp+2080], ecx
	mov DWORD PTR [esp+2084], ecx
	mov DWORD PTR [esp+2088], ecx
	mov DWORD PTR [esp+2092], ecx
	mov DWORD PTR [esp+2096], ecx
	mov DWORD PTR [esp+2100], ecx
	mov DWORD PTR [esp+2104], ecx
	mov DWORD PTR [esp+2108], ecx
	mov DWORD PTR [esp+2112], ecx
	mov DWORD PTR [esp+2116], ecx
	mov DWORD PTR [esp+2120], ecx
	mov DWORD PTR [esp+2124], ecx
	mov DWORD PTR [esp+2128], ecx
	mov DWORD PTR [esp+2132], ecx
	mov DWORD PTR [esp+2136], ecx
	mov DWORD PTR [esp+2140], ecx
	mov DWORD PTR [esp+2144], ecx
	mov DWORD PTR [esp+2148], ecx
	mov DWORD PTR [esp+2152], ecx
	mov DWORD PTR [esp+2156], ecx
	mov DWORD PTR [esp+2160], ecx
	mov DWORD PTR [esp+2164], ecx
	mov DWORD PTR [esp+2168], ecx
	mov DWORD PTR [esp+2172], ecx
	mov DWORD PTR [esp+2176], ecx
	mov DWORD PTR [esp+2180], ecx
	mov DWORD PTR [esp+2184], ecx
	mov DWORD PTR [esp+2188], ecx
	mov DWORD PTR [esp+2192], ecx
	mov DWORD PTR [esp+2196], ecx
	mov DWORD PTR [esp+2200], ecx
	mov DWORD PTR [esp+2204], ecx
	mov DWORD PTR [esp+2208], ecx
	mov DWORD PTR [esp+2212], ecx
	mov DWORD PTR [esp+2216], ecx
	mov DWORD PTR [esp+2220], ecx
	mov DWORD PTR [esp+2224], ecx
	mov DWORD PTR [esp+2228], ecx
	mov DWORD PTR [esp+2232], ecx
	mov DWORD PTR [esp+2236], ecx
	mov DWORD PTR [esp+2240], ecx
	mov DWORD PTR [esp+2244], ecx
	mov DWORD PTR [esp+2248], ecx
	mov DWORD PTR [esp+2252], ecx
	mov DWORD PTR [esp+2256], ecx
	mov DWORD PTR [esp+2260], ecx
	mov DWORD PTR [esp+2264], ecx
	mov DWORD PTR [esp+2268], ecx
	mov DWORD PTR [esp+2272], ecx
	mov DWORD PTR [esp+2276], ecx
	mov DWORD PTR [esp+2280], ecx
	mov DWORD PTR [esp+2284], ecx
	mov DWORD PTR [esp+2288], ecx
	mov DWORD PTR [esp+2292], ecx
	mov DWORD PTR [esp+2296], ecx
	mov DWORD PTR [esp+2300], ecx
	mov DWORD PTR [esp+2304], ecx
	mov DWORD PTR [esp+2308], ecx
	mov DWORD PTR [esp+2312], ecx
	mov DWORD PTR [esp+2316], ecx
	mov DWORD PTR [esp+2320], ecx
	mov DWORD PTR [esp+2324], ecx
	mov DWORD PTR [esp+2328], ecx
	mov DWORD PTR [esp+2332], ecx
	mov DWORD PTR [esp+2336], ecx
	mov DWORD PTR [esp+2340], ecx
	mov DWORD PTR [esp+2344], ecx
	mov DWORD PTR [esp+2348], ecx
	mov DWORD PTR [esp+2352], ecx
	mov DWORD PTR [esp+2356], ecx
	mov DWORD PTR [esp+2360], ecx
	mov DWORD PTR [esp+2364], ecx
	mov DWORD PTR [esp+2368], ecx
	mov DWORD PTR [esp+2372], ecx
	mov DWORD PTR [esp+2376], ecx
	mov DWORD PTR [esp+2380], ecx
	mov DWORD PTR [esp+2384], ecx
	mov DWORD PTR [esp+2388], ecx
	mov DWORD PTR [esp+2392], ecx
	mov DWORD PTR [esp+2396], ecx
	mov DWORD PTR [esp+2400], ecx
	mov DWORD PTR [esp+2404], ecx
	mov DWORD PTR [esp+2408], ecx
	mov DWORD PTR [esp+2412], ecx
	mov DWORD PTR [esp+2416], ecx
	mov DWORD PTR [esp+2420], ecx
	mov DWORD PTR [esp+2424], ecx
	mov DWORD PTR [esp+2428], ecx
	mov DWORD PTR [esp+2432], ecx
	mov DWORD PTR [esp+2436], ecx
	mov DWORD PTR [esp+2440], ecx
	mov DWORD PTR [esp+2444], ecx
	mov DWORD PTR [esp+2448], ecx
	mov DWORD PTR [esp+2452], ecx
	mov DWORD PTR [esp+2456], ecx
	mov DWORD PTR [esp+2460], ecx
	mov DWORD PTR [esp+2464], ecx
	mov DWORD PTR [esp+2468], ecx
	mov DWORD PTR [esp+2472], ecx
	mov DWORD PTR [esp+2476], ecx
	mov DWORD PTR [esp+2480], ecx
	mov DWORD PTR [esp+2484], ecx
	mov DWORD PTR [esp+2488], ecx
	mov DWORD PTR [esp+2492], ecx
	mov DWORD PTR [esp+2496], ecx
	mov DWORD PTR [esp+2500], ecx
	mov DWORD PTR [esp+2504], ecx
	mov DWORD PTR [esp+2508], ecx
	mov DWORD PTR [esp+2512], ecx
	mov DWORD PTR [esp+2516], ecx
	mov DWORD PTR [esp+2520], ecx
	mov DWORD PTR [esp+2524], ecx
	mov DWORD PTR [esp+2528], ecx
	mov DWORD PTR [esp+2532], ecx
	mov DWORD PTR [esp+2536], ecx
	mov DWORD PTR [esp+2540], ecx
	mov DWORD PTR [esp+2544], ecx
	mov DWORD PTR [esp+2548], ecx
	mov DWORD PTR [esp+2552], ecx
	mov DWORD PTR [esp+2556], ecx
	mov DWORD PTR [esp+2560], ecx
	mov DWORD PTR [esp+2564], ecx
	mov DWORD PTR [esp+2568], ecx
	mov DWORD PTR [esp+2572], ecx
	mov DWORD PTR [esp+2576], ecx
	mov DWORD PTR [esp+2580], ecx
	mov DWORD PTR [esp+2584], ecx
	mov DWORD PTR [esp+2588], ecx
	mov DWORD PTR [esp+2592], ecx
	mov DWORD PTR [esp+2596], ecx
	mov DWORD PTR [esp+2600], ecx
	mov DWORD PTR [esp+2604], ecx
	mov DWORD PTR [esp+2608], ecx
	mov DWORD PTR [esp+2612], ecx
	mov DWORD PTR [esp+2616], ecx
	mov DWORD PTR [esp+2620], ecx
	mov DWORD PTR [esp+2624], ecx
	mov DWORD PTR [esp+2628], ecx
	mov DWORD PTR [esp+2632], ecx
	mov DWORD PTR [esp+2636], ecx
	mov DWORD PTR [esp+2640], ecx
	mov DWORD PTR [esp+2644], ecx
	mov DWORD PTR [esp+2648], ecx
	mov DWORD PTR [esp+2652], ecx
	mov DWORD PTR [esp+2656], ecx
	mov DWORD PTR [esp+2660], ecx
	mov DWORD PTR [esp+2664], ecx
	mov DWORD PTR [esp+2668], ecx
	mov DWORD PTR [esp+2672], ecx
	mov DWORD PTR [esp+2676], ecx
	mov DWORD PTR [esp+2680], ecx
	mov DWORD PTR [esp+2684], ecx
	mov DWORD PTR [esp+2688], ecx
	mov DWORD PTR [esp+2692], ecx
	mov DWORD PTR [esp+2696], ecx
	mov DWORD PTR [esp+2700], ecx
	mov DWORD PTR [esp+2704], ecx
	mov DWORD PTR [esp+2708], ecx
	mov DWORD PTR [esp+2712], ecx
	mov DWORD PTR [esp+2716], ecx
	mov DWORD PTR [esp+2720], ecx
	mov DWORD PTR [esp+2724], ecx
	mov DWORD PTR [esp+2728], ecx
	mov DWORD PTR [esp+2732], ecx
	mov DWORD PTR [esp+2736], ecx
	mov DWORD PTR [esp+2740], ecx
	mov DWORD PTR [esp+2744], ecx
	mov DWORD PTR [esp+2748], ecx
	mov DWORD PTR [esp+2752], ecx
	lea esp, [esp+2756]
	ret
	.p2align 6
