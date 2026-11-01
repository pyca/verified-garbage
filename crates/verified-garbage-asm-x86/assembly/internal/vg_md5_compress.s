// The functions of `src/internal/vg_md5_compress.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_compress:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov esi, DWORD PTR [esp+8]
	mov ebp, DWORD PTR [esp+12]
	test ebp, ebp
	je 20f
22:
	mov edi, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, DWORD PTR [edi+8]
	mov edx, DWORD PTR [edi+12]
	mov edi, ecx
	xor edi, edx
	and edi, ebx
	xor edi, edx
	add eax, edi
	add eax, DWORD PTR [esi]
	add eax, -680876936
	ror eax, 25
	add eax, ebx
	mov edi, ebx
	xor edi, ecx
	and edi, eax
	xor edi, ecx
	add edx, edi
	add edx, DWORD PTR [esi+4]
	add edx, -389564586
	ror edx, 20
	add edx, eax
	mov edi, eax
	xor edi, ebx
	and edi, edx
	xor edi, ebx
	add ecx, edi
	add ecx, DWORD PTR [esi+8]
	add ecx, 606105819
	ror ecx, 15
	add ecx, edx
	mov edi, edx
	xor edi, eax
	and edi, ecx
	xor edi, eax
	add ebx, edi
	add ebx, DWORD PTR [esi+12]
	add ebx, -1044525330
	ror ebx, 10
	add ebx, ecx
	mov edi, ecx
	xor edi, edx
	and edi, ebx
	xor edi, edx
	add eax, edi
	add eax, DWORD PTR [esi+16]
	add eax, -176418897
	ror eax, 25
	add eax, ebx
	mov edi, ebx
	xor edi, ecx
	and edi, eax
	xor edi, ecx
	add edx, edi
	add edx, DWORD PTR [esi+20]
	add edx, 1200080426
	ror edx, 20
	add edx, eax
	mov edi, eax
	xor edi, ebx
	and edi, edx
	xor edi, ebx
	add ecx, edi
	add ecx, DWORD PTR [esi+24]
	add ecx, -1473231341
	ror ecx, 15
	add ecx, edx
	mov edi, edx
	xor edi, eax
	and edi, ecx
	xor edi, eax
	add ebx, edi
	add ebx, DWORD PTR [esi+28]
	add ebx, -45705983
	ror ebx, 10
	add ebx, ecx
	mov edi, ecx
	xor edi, edx
	and edi, ebx
	xor edi, edx
	add eax, edi
	add eax, DWORD PTR [esi+32]
	add eax, 1770035416
	ror eax, 25
	add eax, ebx
	mov edi, ebx
	xor edi, ecx
	and edi, eax
	xor edi, ecx
	add edx, edi
	add edx, DWORD PTR [esi+36]
	add edx, -1958414417
	ror edx, 20
	add edx, eax
	mov edi, eax
	xor edi, ebx
	and edi, edx
	xor edi, ebx
	add ecx, edi
	add ecx, DWORD PTR [esi+40]
	add ecx, -42063
	ror ecx, 15
	add ecx, edx
	mov edi, edx
	xor edi, eax
	and edi, ecx
	xor edi, eax
	add ebx, edi
	add ebx, DWORD PTR [esi+44]
	add ebx, -1990404162
	ror ebx, 10
	add ebx, ecx
	mov edi, ecx
	xor edi, edx
	and edi, ebx
	xor edi, edx
	add eax, edi
	add eax, DWORD PTR [esi+48]
	add eax, 1804603682
	ror eax, 25
	add eax, ebx
	mov edi, ebx
	xor edi, ecx
	and edi, eax
	xor edi, ecx
	add edx, edi
	add edx, DWORD PTR [esi+52]
	add edx, -40341101
	ror edx, 20
	add edx, eax
	mov edi, eax
	xor edi, ebx
	and edi, edx
	xor edi, ebx
	add ecx, edi
	add ecx, DWORD PTR [esi+56]
	add ecx, -1502002290
	ror ecx, 15
	add ecx, edx
	mov edi, edx
	xor edi, eax
	and edi, ecx
	xor edi, eax
	add ebx, edi
	add ebx, DWORD PTR [esi+60]
	add ebx, 1236535329
	ror ebx, 10
	add ebx, ecx
	mov edi, ebx
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	add eax, edi
	add eax, DWORD PTR [esi+4]
	add eax, -165796510
	ror eax, 27
	add eax, ebx
	mov edi, eax
	xor edi, ebx
	and edi, ecx
	xor edi, ebx
	add edx, edi
	add edx, DWORD PTR [esi+24]
	add edx, -1069501632
	ror edx, 23
	add edx, eax
	mov edi, edx
	xor edi, eax
	and edi, ebx
	xor edi, eax
	add ecx, edi
	add ecx, DWORD PTR [esi+44]
	add ecx, 643717713
	ror ecx, 18
	add ecx, edx
	mov edi, ecx
	xor edi, edx
	and edi, eax
	xor edi, edx
	add ebx, edi
	add ebx, DWORD PTR [esi]
	add ebx, -373897302
	ror ebx, 12
	add ebx, ecx
	mov edi, ebx
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	add eax, edi
	add eax, DWORD PTR [esi+20]
	add eax, -701558691
	ror eax, 27
	add eax, ebx
	mov edi, eax
	xor edi, ebx
	and edi, ecx
	xor edi, ebx
	add edx, edi
	add edx, DWORD PTR [esi+40]
	add edx, 38016083
	ror edx, 23
	add edx, eax
	mov edi, edx
	xor edi, eax
	and edi, ebx
	xor edi, eax
	add ecx, edi
	add ecx, DWORD PTR [esi+60]
	add ecx, -660478335
	ror ecx, 18
	add ecx, edx
	mov edi, ecx
	xor edi, edx
	and edi, eax
	xor edi, edx
	add ebx, edi
	add ebx, DWORD PTR [esi+16]
	add ebx, -405537848
	ror ebx, 12
	add ebx, ecx
	mov edi, ebx
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	add eax, edi
	add eax, DWORD PTR [esi+36]
	add eax, 568446438
	ror eax, 27
	add eax, ebx
	mov edi, eax
	xor edi, ebx
	and edi, ecx
	xor edi, ebx
	add edx, edi
	add edx, DWORD PTR [esi+56]
	add edx, -1019803690
	ror edx, 23
	add edx, eax
	mov edi, edx
	xor edi, eax
	and edi, ebx
	xor edi, eax
	add ecx, edi
	add ecx, DWORD PTR [esi+12]
	add ecx, -187363961
	ror ecx, 18
	add ecx, edx
	mov edi, ecx
	xor edi, edx
	and edi, eax
	xor edi, edx
	add ebx, edi
	add ebx, DWORD PTR [esi+32]
	add ebx, 1163531501
	ror ebx, 12
	add ebx, ecx
	mov edi, ebx
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	add eax, edi
	add eax, DWORD PTR [esi+52]
	add eax, -1444681467
	ror eax, 27
	add eax, ebx
	mov edi, eax
	xor edi, ebx
	and edi, ecx
	xor edi, ebx
	add edx, edi
	add edx, DWORD PTR [esi+8]
	add edx, -51403784
	ror edx, 23
	add edx, eax
	mov edi, edx
	xor edi, eax
	and edi, ebx
	xor edi, eax
	add ecx, edi
	add ecx, DWORD PTR [esi+28]
	add ecx, 1735328473
	ror ecx, 18
	add ecx, edx
	mov edi, ecx
	xor edi, edx
	and edi, eax
	xor edi, edx
	add ebx, edi
	add ebx, DWORD PTR [esi+48]
	add ebx, -1926607734
	ror ebx, 12
	add ebx, ecx
	mov edi, ebx
	xor edi, ecx
	xor edi, edx
	add eax, edi
	add eax, DWORD PTR [esi+20]
	add eax, -378558
	ror eax, 28
	add eax, ebx
	mov edi, eax
	xor edi, ebx
	xor edi, ecx
	add edx, edi
	add edx, DWORD PTR [esi+32]
	add edx, -2022574463
	ror edx, 21
	add edx, eax
	mov edi, edx
	xor edi, eax
	xor edi, ebx
	add ecx, edi
	add ecx, DWORD PTR [esi+44]
	add ecx, 1839030562
	ror ecx, 16
	add ecx, edx
	mov edi, ecx
	xor edi, edx
	xor edi, eax
	add ebx, edi
	add ebx, DWORD PTR [esi+56]
	add ebx, -35309556
	ror ebx, 9
	add ebx, ecx
	mov edi, ebx
	xor edi, ecx
	xor edi, edx
	add eax, edi
	add eax, DWORD PTR [esi+4]
	add eax, -1530992060
	ror eax, 28
	add eax, ebx
	mov edi, eax
	xor edi, ebx
	xor edi, ecx
	add edx, edi
	add edx, DWORD PTR [esi+16]
	add edx, 1272893353
	ror edx, 21
	add edx, eax
	mov edi, edx
	xor edi, eax
	xor edi, ebx
	add ecx, edi
	add ecx, DWORD PTR [esi+28]
	add ecx, -155497632
	ror ecx, 16
	add ecx, edx
	mov edi, ecx
	xor edi, edx
	xor edi, eax
	add ebx, edi
	add ebx, DWORD PTR [esi+40]
	add ebx, -1094730640
	ror ebx, 9
	add ebx, ecx
	mov edi, ebx
	xor edi, ecx
	xor edi, edx
	add eax, edi
	add eax, DWORD PTR [esi+52]
	add eax, 681279174
	ror eax, 28
	add eax, ebx
	mov edi, eax
	xor edi, ebx
	xor edi, ecx
	add edx, edi
	add edx, DWORD PTR [esi]
	add edx, -358537222
	ror edx, 21
	add edx, eax
	mov edi, edx
	xor edi, eax
	xor edi, ebx
	add ecx, edi
	add ecx, DWORD PTR [esi+12]
	add ecx, -722521979
	ror ecx, 16
	add ecx, edx
	mov edi, ecx
	xor edi, edx
	xor edi, eax
	add ebx, edi
	add ebx, DWORD PTR [esi+24]
	add ebx, 76029189
	ror ebx, 9
	add ebx, ecx
	mov edi, ebx
	xor edi, ecx
	xor edi, edx
	add eax, edi
	add eax, DWORD PTR [esi+36]
	add eax, -640364487
	ror eax, 28
	add eax, ebx
	mov edi, eax
	xor edi, ebx
	xor edi, ecx
	add edx, edi
	add edx, DWORD PTR [esi+48]
	add edx, -421815835
	ror edx, 21
	add edx, eax
	mov edi, edx
	xor edi, eax
	xor edi, ebx
	add ecx, edi
	add ecx, DWORD PTR [esi+60]
	add ecx, 530742520
	ror ecx, 16
	add ecx, edx
	mov edi, ecx
	xor edi, edx
	xor edi, eax
	add ebx, edi
	add ebx, DWORD PTR [esi+8]
	add ebx, -995338651
	ror ebx, 9
	add ebx, ecx
	mov edi, edx
	xor edi, -1
	or edi, ebx
	xor edi, ecx
	add eax, edi
	add eax, DWORD PTR [esi]
	add eax, -198630844
	ror eax, 26
	add eax, ebx
	mov edi, ecx
	xor edi, -1
	or edi, eax
	xor edi, ebx
	add edx, edi
	add edx, DWORD PTR [esi+28]
	add edx, 1126891415
	ror edx, 22
	add edx, eax
	mov edi, ebx
	xor edi, -1
	or edi, edx
	xor edi, eax
	add ecx, edi
	add ecx, DWORD PTR [esi+56]
	add ecx, -1416354905
	ror ecx, 17
	add ecx, edx
	mov edi, eax
	xor edi, -1
	or edi, ecx
	xor edi, edx
	add ebx, edi
	add ebx, DWORD PTR [esi+20]
	add ebx, -57434055
	ror ebx, 11
	add ebx, ecx
	mov edi, edx
	xor edi, -1
	or edi, ebx
	xor edi, ecx
	add eax, edi
	add eax, DWORD PTR [esi+48]
	add eax, 1700485571
	ror eax, 26
	add eax, ebx
	mov edi, ecx
	xor edi, -1
	or edi, eax
	xor edi, ebx
	add edx, edi
	add edx, DWORD PTR [esi+12]
	add edx, -1894986606
	ror edx, 22
	add edx, eax
	mov edi, ebx
	xor edi, -1
	or edi, edx
	xor edi, eax
	add ecx, edi
	add ecx, DWORD PTR [esi+40]
	add ecx, -1051523
	ror ecx, 17
	add ecx, edx
	mov edi, eax
	xor edi, -1
	or edi, ecx
	xor edi, edx
	add ebx, edi
	add ebx, DWORD PTR [esi+4]
	add ebx, -2054922799
	ror ebx, 11
	add ebx, ecx
	mov edi, edx
	xor edi, -1
	or edi, ebx
	xor edi, ecx
	add eax, edi
	add eax, DWORD PTR [esi+32]
	add eax, 1873313359
	ror eax, 26
	add eax, ebx
	mov edi, ecx
	xor edi, -1
	or edi, eax
	xor edi, ebx
	add edx, edi
	add edx, DWORD PTR [esi+60]
	add edx, -30611744
	ror edx, 22
	add edx, eax
	mov edi, ebx
	xor edi, -1
	or edi, edx
	xor edi, eax
	add ecx, edi
	add ecx, DWORD PTR [esi+24]
	add ecx, -1560198380
	ror ecx, 17
	add ecx, edx
	mov edi, eax
	xor edi, -1
	or edi, ecx
	xor edi, edx
	add ebx, edi
	add ebx, DWORD PTR [esi+52]
	add ebx, 1309151649
	ror ebx, 11
	add ebx, ecx
	mov edi, edx
	xor edi, -1
	or edi, ebx
	xor edi, ecx
	add eax, edi
	add eax, DWORD PTR [esi+16]
	add eax, -145523070
	ror eax, 26
	add eax, ebx
	mov edi, ecx
	xor edi, -1
	or edi, eax
	xor edi, ebx
	add edx, edi
	add edx, DWORD PTR [esi+44]
	add edx, -1120210379
	ror edx, 22
	add edx, eax
	mov edi, ebx
	xor edi, -1
	or edi, edx
	xor edi, eax
	add ecx, edi
	add ecx, DWORD PTR [esi+8]
	add ecx, 718787259
	ror ecx, 17
	add ecx, edx
	mov edi, eax
	xor edi, -1
	or edi, ecx
	xor edi, edx
	add ebx, edi
	add ebx, DWORD PTR [esi+36]
	add ebx, -343485551
	ror ebx, 11
	add ebx, ecx
	mov edi, DWORD PTR [esp+4]
	add eax, DWORD PTR [edi]
	add ebx, DWORD PTR [edi+4]
	add ecx, DWORD PTR [edi+8]
	add edx, DWORD PTR [edi+12]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov DWORD PTR [edi+8], ecx
	mov DWORD PTR [edi+12], edx
	add esi, 64
	sub ebp, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+16]
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov edi, DWORD PTR [eax+8]
	mov ebp, DWORD PTR [eax+12]
	ret
	.p2align 6
