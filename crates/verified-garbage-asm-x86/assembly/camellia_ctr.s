// The functions of `src/camellia_ctr.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_ctr:
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
	mov eax, DWORD PTR [edi+2708]
	cmp eax, 8
	jb 24f
26:
	mov esi, DWORD PTR [edi+2704]
	mov ebp, DWORD PTR [edi+2708]
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+2724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+2724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+2724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+2724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+2724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+2724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+2724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+2724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2712], eax
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
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+288]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+292]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+296]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+300]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+304]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+308]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+312]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+316]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [edi+320]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [edi+324]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [edi+328]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [edi+332]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [edi+336]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [edi+340]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [edi+344]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [edi+348]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [esi+64]
	xor eax, DWORD PTR [edi+352]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+68]
	xor eax, DWORD PTR [edi+356]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+72]
	xor eax, DWORD PTR [edi+360]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+76]
	xor eax, DWORD PTR [edi+364]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [edi+368]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [edi+372]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [edi+376]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [edi+380]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+96]
	xor eax, DWORD PTR [edi+384]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [esi+100]
	xor eax, DWORD PTR [edi+388]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [esi+104]
	xor eax, DWORD PTR [edi+392]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [esi+108]
	xor eax, DWORD PTR [edi+396]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [esi+112]
	xor eax, DWORD PTR [edi+400]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [esi+116]
	xor eax, DWORD PTR [edi+404]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [esi+120]
	xor eax, DWORD PTR [edi+408]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [esi+124]
	xor eax, DWORD PTR [edi+412]
	mov DWORD PTR [esi+124], eax
	add esi, 128
	sub ebp, 8
	mov DWORD PTR [edi+2704], esi
	mov DWORD PTR [edi+2708], ebp
	cmp ebp, 8
	jae 26b
	jmp 25f
24:
25:
	mov eax, DWORD PTR [edi+2708]
	cmp eax, 4
	jb 27f
29:
	mov esi, DWORD PTR [edi+2704]
	mov ebp, DWORD PTR [edi+2708]
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+2724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+2724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+2724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+2724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2712], eax
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
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+288]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+292]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+296]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+300]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+304]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+308]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+312]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+316]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [edi+320]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [edi+324]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [edi+328]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [edi+332]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [edi+336]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [edi+340]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [edi+344]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [edi+348]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+2704], esi
	mov DWORD PTR [edi+2708], ebp
	cmp ebp, 4
	jae 29b
	jmp 28f
27:
28:
	mov eax, DWORD PTR [edi+2708]
	cmp eax, 2
	jb 210f
212:
	mov esi, DWORD PTR [edi+2704]
	mov ebp, DWORD PTR [edi+2708]
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+2724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+2724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2712], eax
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
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+288]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+292]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+296]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+300]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+304]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+308]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+312]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+316]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+2704], esi
	mov DWORD PTR [edi+2708], ebp
	cmp ebp, 2
	jae 212b
	jmp 211f
210:
211:
	mov eax, DWORD PTR [edi+2708]
	test eax, eax
	je 213f
215:
	mov esi, DWORD PTR [edi+2704]
	mov ebp, DWORD PTR [edi+2708]
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+2724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+2712], eax
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
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+288]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+292]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+296]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+300]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+2704], esi
	mov DWORD PTR [edi+2708], ebp
	jne 215b
	jmp 214f
213:
214:
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
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+28], xmm0
	movdqu XMMWORD PTR [esp+44], xmm0
	movdqu XMMWORD PTR [esp+60], xmm0
	movdqu XMMWORD PTR [esp+76], xmm0
	movdqu XMMWORD PTR [esp+92], xmm0
	movdqu XMMWORD PTR [esp+108], xmm0
	movdqu XMMWORD PTR [esp+124], xmm0
	movdqu XMMWORD PTR [esp+140], xmm0
	movdqu XMMWORD PTR [esp+156], xmm0
	movdqu XMMWORD PTR [esp+172], xmm0
	movdqu XMMWORD PTR [esp+188], xmm0
	movdqu XMMWORD PTR [esp+204], xmm0
	movdqu XMMWORD PTR [esp+220], xmm0
	movdqu XMMWORD PTR [esp+236], xmm0
	movdqu XMMWORD PTR [esp+252], xmm0
	movdqu XMMWORD PTR [esp+268], xmm0
	movdqu XMMWORD PTR [esp+284], xmm0
	movdqu XMMWORD PTR [esp+300], xmm0
	movdqu XMMWORD PTR [esp+316], xmm0
	movdqu XMMWORD PTR [esp+332], xmm0
	movdqu XMMWORD PTR [esp+348], xmm0
	movdqu XMMWORD PTR [esp+364], xmm0
	movdqu XMMWORD PTR [esp+380], xmm0
	movdqu XMMWORD PTR [esp+396], xmm0
	movdqu XMMWORD PTR [esp+412], xmm0
	movdqu XMMWORD PTR [esp+428], xmm0
	movdqu XMMWORD PTR [esp+444], xmm0
	movdqu XMMWORD PTR [esp+460], xmm0
	movdqu XMMWORD PTR [esp+476], xmm0
	movdqu XMMWORD PTR [esp+492], xmm0
	movdqu XMMWORD PTR [esp+508], xmm0
	movdqu XMMWORD PTR [esp+524], xmm0
	movdqu XMMWORD PTR [esp+540], xmm0
	movdqu XMMWORD PTR [esp+556], xmm0
	movdqu XMMWORD PTR [esp+572], xmm0
	movdqu XMMWORD PTR [esp+588], xmm0
	movdqu XMMWORD PTR [esp+604], xmm0
	movdqu XMMWORD PTR [esp+620], xmm0
	movdqu XMMWORD PTR [esp+636], xmm0
	movdqu XMMWORD PTR [esp+652], xmm0
	movdqu XMMWORD PTR [esp+668], xmm0
	movdqu XMMWORD PTR [esp+684], xmm0
	movdqu XMMWORD PTR [esp+700], xmm0
	movdqu XMMWORD PTR [esp+716], xmm0
	movdqu XMMWORD PTR [esp+732], xmm0
	movdqu XMMWORD PTR [esp+748], xmm0
	movdqu XMMWORD PTR [esp+764], xmm0
	movdqu XMMWORD PTR [esp+780], xmm0
	movdqu XMMWORD PTR [esp+796], xmm0
	movdqu XMMWORD PTR [esp+812], xmm0
	movdqu XMMWORD PTR [esp+828], xmm0
	movdqu XMMWORD PTR [esp+844], xmm0
	movdqu XMMWORD PTR [esp+860], xmm0
	movdqu XMMWORD PTR [esp+876], xmm0
	movdqu XMMWORD PTR [esp+892], xmm0
	movdqu XMMWORD PTR [esp+908], xmm0
	movdqu XMMWORD PTR [esp+924], xmm0
	movdqu XMMWORD PTR [esp+940], xmm0
	movdqu XMMWORD PTR [esp+956], xmm0
	movdqu XMMWORD PTR [esp+972], xmm0
	movdqu XMMWORD PTR [esp+988], xmm0
	movdqu XMMWORD PTR [esp+1004], xmm0
	movdqu XMMWORD PTR [esp+1020], xmm0
	movdqu XMMWORD PTR [esp+1036], xmm0
	movdqu XMMWORD PTR [esp+1052], xmm0
	movdqu XMMWORD PTR [esp+1068], xmm0
	movdqu XMMWORD PTR [esp+1084], xmm0
	movdqu XMMWORD PTR [esp+1100], xmm0
	movdqu XMMWORD PTR [esp+1116], xmm0
	movdqu XMMWORD PTR [esp+1132], xmm0
	movdqu XMMWORD PTR [esp+1148], xmm0
	movdqu XMMWORD PTR [esp+1164], xmm0
	movdqu XMMWORD PTR [esp+1180], xmm0
	movdqu XMMWORD PTR [esp+1196], xmm0
	movdqu XMMWORD PTR [esp+1212], xmm0
	movdqu XMMWORD PTR [esp+1228], xmm0
	movdqu XMMWORD PTR [esp+1244], xmm0
	movdqu XMMWORD PTR [esp+1260], xmm0
	movdqu XMMWORD PTR [esp+1276], xmm0
	movdqu XMMWORD PTR [esp+1292], xmm0
	movdqu XMMWORD PTR [esp+1308], xmm0
	movdqu XMMWORD PTR [esp+1324], xmm0
	movdqu XMMWORD PTR [esp+1340], xmm0
	movdqu XMMWORD PTR [esp+1356], xmm0
	movdqu XMMWORD PTR [esp+1372], xmm0
	movdqu XMMWORD PTR [esp+1388], xmm0
	movdqu XMMWORD PTR [esp+1404], xmm0
	movdqu XMMWORD PTR [esp+1420], xmm0
	movdqu XMMWORD PTR [esp+1436], xmm0
	movdqu XMMWORD PTR [esp+1452], xmm0
	movdqu XMMWORD PTR [esp+1468], xmm0
	movdqu XMMWORD PTR [esp+1484], xmm0
	movdqu XMMWORD PTR [esp+1500], xmm0
	movdqu XMMWORD PTR [esp+1516], xmm0
	movdqu XMMWORD PTR [esp+1532], xmm0
	movdqu XMMWORD PTR [esp+1548], xmm0
	movdqu XMMWORD PTR [esp+1564], xmm0
	movdqu XMMWORD PTR [esp+1580], xmm0
	movdqu XMMWORD PTR [esp+1596], xmm0
	movdqu XMMWORD PTR [esp+1612], xmm0
	movdqu XMMWORD PTR [esp+1628], xmm0
	movdqu XMMWORD PTR [esp+1644], xmm0
	movdqu XMMWORD PTR [esp+1660], xmm0
	movdqu XMMWORD PTR [esp+1676], xmm0
	movdqu XMMWORD PTR [esp+1692], xmm0
	movdqu XMMWORD PTR [esp+1708], xmm0
	movdqu XMMWORD PTR [esp+1724], xmm0
	movdqu XMMWORD PTR [esp+1740], xmm0
	movdqu XMMWORD PTR [esp+1756], xmm0
	movdqu XMMWORD PTR [esp+1772], xmm0
	movdqu XMMWORD PTR [esp+1788], xmm0
	movdqu XMMWORD PTR [esp+1804], xmm0
	movdqu XMMWORD PTR [esp+1820], xmm0
	movdqu XMMWORD PTR [esp+1836], xmm0
	movdqu XMMWORD PTR [esp+1852], xmm0
	movdqu XMMWORD PTR [esp+1868], xmm0
	movdqu XMMWORD PTR [esp+1884], xmm0
	movdqu XMMWORD PTR [esp+1900], xmm0
	movdqu XMMWORD PTR [esp+1916], xmm0
	movdqu XMMWORD PTR [esp+1932], xmm0
	movdqu XMMWORD PTR [esp+1948], xmm0
	movdqu XMMWORD PTR [esp+1964], xmm0
	movdqu XMMWORD PTR [esp+1980], xmm0
	movdqu XMMWORD PTR [esp+1996], xmm0
	movdqu XMMWORD PTR [esp+2012], xmm0
	movdqu XMMWORD PTR [esp+2028], xmm0
	movdqu XMMWORD PTR [esp+2044], xmm0
	movdqu XMMWORD PTR [esp+2060], xmm0
	movdqu XMMWORD PTR [esp+2076], xmm0
	movdqu XMMWORD PTR [esp+2092], xmm0
	movdqu XMMWORD PTR [esp+2108], xmm0
	movdqu XMMWORD PTR [esp+2124], xmm0
	movdqu XMMWORD PTR [esp+2140], xmm0
	movdqu XMMWORD PTR [esp+2156], xmm0
	movdqu XMMWORD PTR [esp+2172], xmm0
	movdqu XMMWORD PTR [esp+2188], xmm0
	movdqu XMMWORD PTR [esp+2204], xmm0
	movdqu XMMWORD PTR [esp+2220], xmm0
	movdqu XMMWORD PTR [esp+2236], xmm0
	movdqu XMMWORD PTR [esp+2252], xmm0
	movdqu XMMWORD PTR [esp+2268], xmm0
	movdqu XMMWORD PTR [esp+2284], xmm0
	movdqu XMMWORD PTR [esp+2300], xmm0
	movdqu XMMWORD PTR [esp+2316], xmm0
	movdqu XMMWORD PTR [esp+2332], xmm0
	movdqu XMMWORD PTR [esp+2348], xmm0
	movdqu XMMWORD PTR [esp+2364], xmm0
	movdqu XMMWORD PTR [esp+2380], xmm0
	movdqu XMMWORD PTR [esp+2396], xmm0
	movdqu XMMWORD PTR [esp+2412], xmm0
	movdqu XMMWORD PTR [esp+2428], xmm0
	movdqu XMMWORD PTR [esp+2444], xmm0
	movdqu XMMWORD PTR [esp+2460], xmm0
	movdqu XMMWORD PTR [esp+2476], xmm0
	movdqu XMMWORD PTR [esp+2492], xmm0
	movdqu XMMWORD PTR [esp+2508], xmm0
	movdqu XMMWORD PTR [esp+2524], xmm0
	movdqu XMMWORD PTR [esp+2540], xmm0
	movdqu XMMWORD PTR [esp+2556], xmm0
	movdqu XMMWORD PTR [esp+2572], xmm0
	movdqu XMMWORD PTR [esp+2588], xmm0
	movdqu XMMWORD PTR [esp+2604], xmm0
	movdqu XMMWORD PTR [esp+2620], xmm0
	movdqu XMMWORD PTR [esp+2636], xmm0
	movdqu XMMWORD PTR [esp+2652], xmm0
	movdqu XMMWORD PTR [esp+2668], xmm0
	movdqu XMMWORD PTR [esp+2684], xmm0
	movdqu XMMWORD PTR [esp+2700], xmm0
	movdqu XMMWORD PTR [esp+2716], xmm0
	movdqu XMMWORD PTR [esp+2732], xmm0
	mov DWORD PTR [esp+2748], ecx
	mov DWORD PTR [esp+2752], ecx
	lea esp, [esp+2756]
	lea esp, [esp-2772]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	lea esp, [esp+2772]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_camellia_ctr_final:
	lea esp, [esp-60]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+16]
	mov esi, DWORD PTR [esp+20]
	shr esi, 4
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_camellia_ctr_core}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	and eax, 15
	test eax, eax
	je 20f
	mov eax, DWORD PTR [esp+24]
	mov ecx, 0
	mov DWORD PTR [eax+16], ecx
	mov DWORD PTR [eax+20], ecx
	mov DWORD PTR [eax+24], ecx
	mov DWORD PTR [eax+28], ecx
	mov ebx, eax
	add ebx, 16
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	mov esi, 1
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_camellia_ctr_core}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+24]
	add ebx, 16
	mov esi, DWORD PTR [esp+16]
	mov ebp, DWORD PTR [esp+20]
	mov eax, ebp
	and ebp, 15
	sub eax, ebp
	add esi, eax
22:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov edi, DWORD PTR [eax+8]
	mov ebp, DWORD PTR [eax+12]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+28], xmm0
	movdqu XMMWORD PTR [esp+44], xmm0
	lea esp, [esp+60]
	lea esp, [esp-2856]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+2772], ecx
	mov DWORD PTR [esp+2776], ecx
	mov DWORD PTR [esp+2780], ecx
	mov DWORD PTR [esp+2784], ecx
	mov DWORD PTR [esp+2788], ecx
	mov DWORD PTR [esp+2792], ecx
	mov DWORD PTR [esp+2796], ecx
	mov DWORD PTR [esp+2800], ecx
	mov DWORD PTR [esp+2804], ecx
	mov DWORD PTR [esp+2808], ecx
	mov DWORD PTR [esp+2812], ecx
	mov DWORD PTR [esp+2816], ecx
	mov DWORD PTR [esp+2820], ecx
	lea esp, [esp+2856]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6
