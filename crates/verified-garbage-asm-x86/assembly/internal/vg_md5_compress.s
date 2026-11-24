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
	add eax, DWORD PTR [esi]
	add eax, -680876936
	mov edi, ecx
	xor edi, edx
	and edi, ebx
	xor edi, edx
	add eax, edi
	ror eax, 25
	add eax, ebx
	add edx, DWORD PTR [esi+4]
	add edx, -389564586
	mov edi, ebx
	xor edi, ecx
	and edi, eax
	xor edi, ecx
	add edx, edi
	ror edx, 20
	add edx, eax
	add ecx, DWORD PTR [esi+8]
	add ecx, 606105819
	mov edi, eax
	xor edi, ebx
	and edi, edx
	xor edi, ebx
	add ecx, edi
	ror ecx, 15
	add ecx, edx
	add ebx, DWORD PTR [esi+12]
	add ebx, -1044525330
	mov edi, edx
	xor edi, eax
	and edi, ecx
	xor edi, eax
	add ebx, edi
	ror ebx, 10
	add ebx, ecx
	add eax, DWORD PTR [esi+16]
	add eax, -176418897
	mov edi, ecx
	xor edi, edx
	and edi, ebx
	xor edi, edx
	add eax, edi
	ror eax, 25
	add eax, ebx
	add edx, DWORD PTR [esi+20]
	add edx, 1200080426
	mov edi, ebx
	xor edi, ecx
	and edi, eax
	xor edi, ecx
	add edx, edi
	ror edx, 20
	add edx, eax
	add ecx, DWORD PTR [esi+24]
	add ecx, -1473231341
	mov edi, eax
	xor edi, ebx
	and edi, edx
	xor edi, ebx
	add ecx, edi
	ror ecx, 15
	add ecx, edx
	add ebx, DWORD PTR [esi+28]
	add ebx, -45705983
	mov edi, edx
	xor edi, eax
	and edi, ecx
	xor edi, eax
	add ebx, edi
	ror ebx, 10
	add ebx, ecx
	add eax, DWORD PTR [esi+32]
	add eax, 1770035416
	mov edi, ecx
	xor edi, edx
	and edi, ebx
	xor edi, edx
	add eax, edi
	ror eax, 25
	add eax, ebx
	add edx, DWORD PTR [esi+36]
	add edx, -1958414417
	mov edi, ebx
	xor edi, ecx
	and edi, eax
	xor edi, ecx
	add edx, edi
	ror edx, 20
	add edx, eax
	add ecx, DWORD PTR [esi+40]
	add ecx, -42063
	mov edi, eax
	xor edi, ebx
	and edi, edx
	xor edi, ebx
	add ecx, edi
	ror ecx, 15
	add ecx, edx
	add ebx, DWORD PTR [esi+44]
	add ebx, -1990404162
	mov edi, edx
	xor edi, eax
	and edi, ecx
	xor edi, eax
	add ebx, edi
	ror ebx, 10
	add ebx, ecx
	add eax, DWORD PTR [esi+48]
	add eax, 1804603682
	mov edi, ecx
	xor edi, edx
	and edi, ebx
	xor edi, edx
	add eax, edi
	ror eax, 25
	add eax, ebx
	add edx, DWORD PTR [esi+52]
	add edx, -40341101
	mov edi, ebx
	xor edi, ecx
	and edi, eax
	xor edi, ecx
	add edx, edi
	ror edx, 20
	add edx, eax
	add ecx, DWORD PTR [esi+56]
	add ecx, -1502002290
	mov edi, eax
	xor edi, ebx
	and edi, edx
	xor edi, ebx
	add ecx, edi
	ror ecx, 15
	add ecx, edx
	add ebx, DWORD PTR [esi+60]
	add ebx, 1236535329
	mov edi, edx
	xor edi, eax
	and edi, ecx
	xor edi, eax
	add ebx, edi
	ror ebx, 10
	add ebx, ecx
	add eax, DWORD PTR [esi+4]
	add eax, -165796510
	mov edi, edx
	xor edi, -1
	and edi, ecx
	add eax, edi
	mov edi, edx
	and edi, ebx
	add eax, edi
	ror eax, 27
	add eax, ebx
	add edx, DWORD PTR [esi+24]
	add edx, -1069501632
	mov edi, ecx
	xor edi, -1
	and edi, ebx
	add edx, edi
	mov edi, ecx
	and edi, eax
	add edx, edi
	ror edx, 23
	add edx, eax
	add ecx, DWORD PTR [esi+44]
	add ecx, 643717713
	mov edi, ebx
	xor edi, -1
	and edi, eax
	add ecx, edi
	mov edi, ebx
	and edi, edx
	add ecx, edi
	ror ecx, 18
	add ecx, edx
	add ebx, DWORD PTR [esi]
	add ebx, -373897302
	mov edi, eax
	xor edi, -1
	and edi, edx
	add ebx, edi
	mov edi, eax
	and edi, ecx
	add ebx, edi
	ror ebx, 12
	add ebx, ecx
	add eax, DWORD PTR [esi+20]
	add eax, -701558691
	mov edi, edx
	xor edi, -1
	and edi, ecx
	add eax, edi
	mov edi, edx
	and edi, ebx
	add eax, edi
	ror eax, 27
	add eax, ebx
	add edx, DWORD PTR [esi+40]
	add edx, 38016083
	mov edi, ecx
	xor edi, -1
	and edi, ebx
	add edx, edi
	mov edi, ecx
	and edi, eax
	add edx, edi
	ror edx, 23
	add edx, eax
	add ecx, DWORD PTR [esi+60]
	add ecx, -660478335
	mov edi, ebx
	xor edi, -1
	and edi, eax
	add ecx, edi
	mov edi, ebx
	and edi, edx
	add ecx, edi
	ror ecx, 18
	add ecx, edx
	add ebx, DWORD PTR [esi+16]
	add ebx, -405537848
	mov edi, eax
	xor edi, -1
	and edi, edx
	add ebx, edi
	mov edi, eax
	and edi, ecx
	add ebx, edi
	ror ebx, 12
	add ebx, ecx
	add eax, DWORD PTR [esi+36]
	add eax, 568446438
	mov edi, edx
	xor edi, -1
	and edi, ecx
	add eax, edi
	mov edi, edx
	and edi, ebx
	add eax, edi
	ror eax, 27
	add eax, ebx
	add edx, DWORD PTR [esi+56]
	add edx, -1019803690
	mov edi, ecx
	xor edi, -1
	and edi, ebx
	add edx, edi
	mov edi, ecx
	and edi, eax
	add edx, edi
	ror edx, 23
	add edx, eax
	add ecx, DWORD PTR [esi+12]
	add ecx, -187363961
	mov edi, ebx
	xor edi, -1
	and edi, eax
	add ecx, edi
	mov edi, ebx
	and edi, edx
	add ecx, edi
	ror ecx, 18
	add ecx, edx
	add ebx, DWORD PTR [esi+32]
	add ebx, 1163531501
	mov edi, eax
	xor edi, -1
	and edi, edx
	add ebx, edi
	mov edi, eax
	and edi, ecx
	add ebx, edi
	ror ebx, 12
	add ebx, ecx
	add eax, DWORD PTR [esi+52]
	add eax, -1444681467
	mov edi, edx
	xor edi, -1
	and edi, ecx
	add eax, edi
	mov edi, edx
	and edi, ebx
	add eax, edi
	ror eax, 27
	add eax, ebx
	add edx, DWORD PTR [esi+8]
	add edx, -51403784
	mov edi, ecx
	xor edi, -1
	and edi, ebx
	add edx, edi
	mov edi, ecx
	and edi, eax
	add edx, edi
	ror edx, 23
	add edx, eax
	add ecx, DWORD PTR [esi+28]
	add ecx, 1735328473
	mov edi, ebx
	xor edi, -1
	and edi, eax
	add ecx, edi
	mov edi, ebx
	and edi, edx
	add ecx, edi
	ror ecx, 18
	add ecx, edx
	add ebx, DWORD PTR [esi+48]
	add ebx, -1926607734
	mov edi, eax
	xor edi, -1
	and edi, edx
	add ebx, edi
	mov edi, eax
	and edi, ecx
	add ebx, edi
	ror ebx, 12
	add ebx, ecx
	add eax, DWORD PTR [esi+20]
	add eax, -378558
	mov edi, ecx
	xor edi, edx
	xor edi, ebx
	add eax, edi
	ror eax, 28
	add eax, ebx
	add edx, DWORD PTR [esi+32]
	add edx, -2022574463
	mov edi, ebx
	xor edi, ecx
	xor edi, eax
	add edx, edi
	ror edx, 21
	add edx, eax
	add ecx, DWORD PTR [esi+44]
	add ecx, 1839030562
	mov edi, eax
	xor edi, ebx
	xor edi, edx
	add ecx, edi
	ror ecx, 16
	add ecx, edx
	add ebx, DWORD PTR [esi+56]
	add ebx, -35309556
	mov edi, edx
	xor edi, eax
	xor edi, ecx
	add ebx, edi
	ror ebx, 9
	add ebx, ecx
	add eax, DWORD PTR [esi+4]
	add eax, -1530992060
	mov edi, ecx
	xor edi, edx
	xor edi, ebx
	add eax, edi
	ror eax, 28
	add eax, ebx
	add edx, DWORD PTR [esi+16]
	add edx, 1272893353
	mov edi, ebx
	xor edi, ecx
	xor edi, eax
	add edx, edi
	ror edx, 21
	add edx, eax
	add ecx, DWORD PTR [esi+28]
	add ecx, -155497632
	mov edi, eax
	xor edi, ebx
	xor edi, edx
	add ecx, edi
	ror ecx, 16
	add ecx, edx
	add ebx, DWORD PTR [esi+40]
	add ebx, -1094730640
	mov edi, edx
	xor edi, eax
	xor edi, ecx
	add ebx, edi
	ror ebx, 9
	add ebx, ecx
	add eax, DWORD PTR [esi+52]
	add eax, 681279174
	mov edi, ecx
	xor edi, edx
	xor edi, ebx
	add eax, edi
	ror eax, 28
	add eax, ebx
	add edx, DWORD PTR [esi]
	add edx, -358537222
	mov edi, ebx
	xor edi, ecx
	xor edi, eax
	add edx, edi
	ror edx, 21
	add edx, eax
	add ecx, DWORD PTR [esi+12]
	add ecx, -722521979
	mov edi, eax
	xor edi, ebx
	xor edi, edx
	add ecx, edi
	ror ecx, 16
	add ecx, edx
	add ebx, DWORD PTR [esi+24]
	add ebx, 76029189
	mov edi, edx
	xor edi, eax
	xor edi, ecx
	add ebx, edi
	ror ebx, 9
	add ebx, ecx
	add eax, DWORD PTR [esi+36]
	add eax, -640364487
	mov edi, ecx
	xor edi, edx
	xor edi, ebx
	add eax, edi
	ror eax, 28
	add eax, ebx
	add edx, DWORD PTR [esi+48]
	add edx, -421815835
	mov edi, ebx
	xor edi, ecx
	xor edi, eax
	add edx, edi
	ror edx, 21
	add edx, eax
	add ecx, DWORD PTR [esi+60]
	add ecx, 530742520
	mov edi, eax
	xor edi, ebx
	xor edi, edx
	add ecx, edi
	ror ecx, 16
	add ecx, edx
	add ebx, DWORD PTR [esi+8]
	add ebx, -995338651
	mov edi, edx
	xor edi, eax
	xor edi, ecx
	add ebx, edi
	ror ebx, 9
	add ebx, ecx
	add eax, DWORD PTR [esi]
	add eax, -198630844
	mov edi, edx
	xor edi, -1
	or edi, ebx
	xor edi, ecx
	add eax, edi
	ror eax, 26
	add eax, ebx
	add edx, DWORD PTR [esi+28]
	add edx, 1126891415
	mov edi, ecx
	xor edi, -1
	or edi, eax
	xor edi, ebx
	add edx, edi
	ror edx, 22
	add edx, eax
	add ecx, DWORD PTR [esi+56]
	add ecx, -1416354905
	mov edi, ebx
	xor edi, -1
	or edi, edx
	xor edi, eax
	add ecx, edi
	ror ecx, 17
	add ecx, edx
	add ebx, DWORD PTR [esi+20]
	add ebx, -57434055
	mov edi, eax
	xor edi, -1
	or edi, ecx
	xor edi, edx
	add ebx, edi
	ror ebx, 11
	add ebx, ecx
	add eax, DWORD PTR [esi+48]
	add eax, 1700485571
	mov edi, edx
	xor edi, -1
	or edi, ebx
	xor edi, ecx
	add eax, edi
	ror eax, 26
	add eax, ebx
	add edx, DWORD PTR [esi+12]
	add edx, -1894986606
	mov edi, ecx
	xor edi, -1
	or edi, eax
	xor edi, ebx
	add edx, edi
	ror edx, 22
	add edx, eax
	add ecx, DWORD PTR [esi+40]
	add ecx, -1051523
	mov edi, ebx
	xor edi, -1
	or edi, edx
	xor edi, eax
	add ecx, edi
	ror ecx, 17
	add ecx, edx
	add ebx, DWORD PTR [esi+4]
	add ebx, -2054922799
	mov edi, eax
	xor edi, -1
	or edi, ecx
	xor edi, edx
	add ebx, edi
	ror ebx, 11
	add ebx, ecx
	add eax, DWORD PTR [esi+32]
	add eax, 1873313359
	mov edi, edx
	xor edi, -1
	or edi, ebx
	xor edi, ecx
	add eax, edi
	ror eax, 26
	add eax, ebx
	add edx, DWORD PTR [esi+60]
	add edx, -30611744
	mov edi, ecx
	xor edi, -1
	or edi, eax
	xor edi, ebx
	add edx, edi
	ror edx, 22
	add edx, eax
	add ecx, DWORD PTR [esi+24]
	add ecx, -1560198380
	mov edi, ebx
	xor edi, -1
	or edi, edx
	xor edi, eax
	add ecx, edi
	ror ecx, 17
	add ecx, edx
	add ebx, DWORD PTR [esi+52]
	add ebx, 1309151649
	mov edi, eax
	xor edi, -1
	or edi, ecx
	xor edi, edx
	add ebx, edi
	ror ebx, 11
	add ebx, ecx
	add eax, DWORD PTR [esi+16]
	add eax, -145523070
	mov edi, edx
	xor edi, -1
	or edi, ebx
	xor edi, ecx
	add eax, edi
	ror eax, 26
	add eax, ebx
	add edx, DWORD PTR [esi+44]
	add edx, -1120210379
	mov edi, ecx
	xor edi, -1
	or edi, eax
	xor edi, ebx
	add edx, edi
	ror edx, 22
	add edx, eax
	add ecx, DWORD PTR [esi+8]
	add ecx, 718787259
	mov edi, ebx
	xor edi, -1
	or edi, edx
	xor edi, eax
	add ecx, edi
	ror ecx, 17
	add ecx, edx
	add ebx, DWORD PTR [esi+36]
	add ebx, -343485551
	mov edi, eax
	xor edi, -1
	or edi, ecx
	xor edi, edx
	add ebx, edi
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
