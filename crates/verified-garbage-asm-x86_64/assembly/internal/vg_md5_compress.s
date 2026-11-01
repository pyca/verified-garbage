// The functions of `src/internal/vg_md5_compress.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_compress:
	test rdx, rdx
	je 20f
	mov eax, DWORD PTR [rdi]
	mov r8d, DWORD PTR [rdi+4]
	mov r9d, DWORD PTR [rdi+8]
	mov r10d, DWORD PTR [rdi+12]
22:
	add eax, DWORD PTR [rsi]
	add eax, -680876936
	mov r11d, r9d
	xor r11d, r10d
	and r11d, r8d
	xor r11d, r10d
	add eax, r11d
	ror eax, 25
	add eax, r8d
	add r10d, DWORD PTR [rsi+4]
	add r10d, -389564586
	mov r11d, r8d
	xor r11d, r9d
	and r11d, eax
	xor r11d, r9d
	add r10d, r11d
	ror r10d, 20
	add r10d, eax
	add r9d, DWORD PTR [rsi+8]
	add r9d, 606105819
	mov r11d, eax
	xor r11d, r8d
	and r11d, r10d
	xor r11d, r8d
	add r9d, r11d
	ror r9d, 15
	add r9d, r10d
	add r8d, DWORD PTR [rsi+12]
	add r8d, -1044525330
	mov r11d, r10d
	xor r11d, eax
	and r11d, r9d
	xor r11d, eax
	add r8d, r11d
	ror r8d, 10
	add r8d, r9d
	add eax, DWORD PTR [rsi+16]
	add eax, -176418897
	mov r11d, r9d
	xor r11d, r10d
	and r11d, r8d
	xor r11d, r10d
	add eax, r11d
	ror eax, 25
	add eax, r8d
	add r10d, DWORD PTR [rsi+20]
	add r10d, 1200080426
	mov r11d, r8d
	xor r11d, r9d
	and r11d, eax
	xor r11d, r9d
	add r10d, r11d
	ror r10d, 20
	add r10d, eax
	add r9d, DWORD PTR [rsi+24]
	add r9d, -1473231341
	mov r11d, eax
	xor r11d, r8d
	and r11d, r10d
	xor r11d, r8d
	add r9d, r11d
	ror r9d, 15
	add r9d, r10d
	add r8d, DWORD PTR [rsi+28]
	add r8d, -45705983
	mov r11d, r10d
	xor r11d, eax
	and r11d, r9d
	xor r11d, eax
	add r8d, r11d
	ror r8d, 10
	add r8d, r9d
	add eax, DWORD PTR [rsi+32]
	add eax, 1770035416
	mov r11d, r9d
	xor r11d, r10d
	and r11d, r8d
	xor r11d, r10d
	add eax, r11d
	ror eax, 25
	add eax, r8d
	add r10d, DWORD PTR [rsi+36]
	add r10d, -1958414417
	mov r11d, r8d
	xor r11d, r9d
	and r11d, eax
	xor r11d, r9d
	add r10d, r11d
	ror r10d, 20
	add r10d, eax
	add r9d, DWORD PTR [rsi+40]
	add r9d, -42063
	mov r11d, eax
	xor r11d, r8d
	and r11d, r10d
	xor r11d, r8d
	add r9d, r11d
	ror r9d, 15
	add r9d, r10d
	add r8d, DWORD PTR [rsi+44]
	add r8d, -1990404162
	mov r11d, r10d
	xor r11d, eax
	and r11d, r9d
	xor r11d, eax
	add r8d, r11d
	ror r8d, 10
	add r8d, r9d
	add eax, DWORD PTR [rsi+48]
	add eax, 1804603682
	mov r11d, r9d
	xor r11d, r10d
	and r11d, r8d
	xor r11d, r10d
	add eax, r11d
	ror eax, 25
	add eax, r8d
	add r10d, DWORD PTR [rsi+52]
	add r10d, -40341101
	mov r11d, r8d
	xor r11d, r9d
	and r11d, eax
	xor r11d, r9d
	add r10d, r11d
	ror r10d, 20
	add r10d, eax
	add r9d, DWORD PTR [rsi+56]
	add r9d, -1502002290
	mov r11d, eax
	xor r11d, r8d
	and r11d, r10d
	xor r11d, r8d
	add r9d, r11d
	ror r9d, 15
	add r9d, r10d
	add r8d, DWORD PTR [rsi+60]
	add r8d, 1236535329
	mov r11d, r10d
	xor r11d, eax
	and r11d, r9d
	xor r11d, eax
	add r8d, r11d
	ror r8d, 10
	add r8d, r9d
	add eax, DWORD PTR [rsi+4]
	add eax, -165796510
	mov r11d, r10d
	xor r11d, -1
	and r11d, r9d
	add eax, r11d
	mov r11d, r10d
	and r11d, r8d
	add eax, r11d
	ror eax, 27
	add eax, r8d
	add r10d, DWORD PTR [rsi+24]
	add r10d, -1069501632
	mov r11d, r9d
	xor r11d, -1
	and r11d, r8d
	add r10d, r11d
	mov r11d, r9d
	and r11d, eax
	add r10d, r11d
	ror r10d, 23
	add r10d, eax
	add r9d, DWORD PTR [rsi+44]
	add r9d, 643717713
	mov r11d, r8d
	xor r11d, -1
	and r11d, eax
	add r9d, r11d
	mov r11d, r8d
	and r11d, r10d
	add r9d, r11d
	ror r9d, 18
	add r9d, r10d
	add r8d, DWORD PTR [rsi]
	add r8d, -373897302
	mov r11d, eax
	xor r11d, -1
	and r11d, r10d
	add r8d, r11d
	mov r11d, eax
	and r11d, r9d
	add r8d, r11d
	ror r8d, 12
	add r8d, r9d
	add eax, DWORD PTR [rsi+20]
	add eax, -701558691
	mov r11d, r10d
	xor r11d, -1
	and r11d, r9d
	add eax, r11d
	mov r11d, r10d
	and r11d, r8d
	add eax, r11d
	ror eax, 27
	add eax, r8d
	add r10d, DWORD PTR [rsi+40]
	add r10d, 38016083
	mov r11d, r9d
	xor r11d, -1
	and r11d, r8d
	add r10d, r11d
	mov r11d, r9d
	and r11d, eax
	add r10d, r11d
	ror r10d, 23
	add r10d, eax
	add r9d, DWORD PTR [rsi+60]
	add r9d, -660478335
	mov r11d, r8d
	xor r11d, -1
	and r11d, eax
	add r9d, r11d
	mov r11d, r8d
	and r11d, r10d
	add r9d, r11d
	ror r9d, 18
	add r9d, r10d
	add r8d, DWORD PTR [rsi+16]
	add r8d, -405537848
	mov r11d, eax
	xor r11d, -1
	and r11d, r10d
	add r8d, r11d
	mov r11d, eax
	and r11d, r9d
	add r8d, r11d
	ror r8d, 12
	add r8d, r9d
	add eax, DWORD PTR [rsi+36]
	add eax, 568446438
	mov r11d, r10d
	xor r11d, -1
	and r11d, r9d
	add eax, r11d
	mov r11d, r10d
	and r11d, r8d
	add eax, r11d
	ror eax, 27
	add eax, r8d
	add r10d, DWORD PTR [rsi+56]
	add r10d, -1019803690
	mov r11d, r9d
	xor r11d, -1
	and r11d, r8d
	add r10d, r11d
	mov r11d, r9d
	and r11d, eax
	add r10d, r11d
	ror r10d, 23
	add r10d, eax
	add r9d, DWORD PTR [rsi+12]
	add r9d, -187363961
	mov r11d, r8d
	xor r11d, -1
	and r11d, eax
	add r9d, r11d
	mov r11d, r8d
	and r11d, r10d
	add r9d, r11d
	ror r9d, 18
	add r9d, r10d
	add r8d, DWORD PTR [rsi+32]
	add r8d, 1163531501
	mov r11d, eax
	xor r11d, -1
	and r11d, r10d
	add r8d, r11d
	mov r11d, eax
	and r11d, r9d
	add r8d, r11d
	ror r8d, 12
	add r8d, r9d
	add eax, DWORD PTR [rsi+52]
	add eax, -1444681467
	mov r11d, r10d
	xor r11d, -1
	and r11d, r9d
	add eax, r11d
	mov r11d, r10d
	and r11d, r8d
	add eax, r11d
	ror eax, 27
	add eax, r8d
	add r10d, DWORD PTR [rsi+8]
	add r10d, -51403784
	mov r11d, r9d
	xor r11d, -1
	and r11d, r8d
	add r10d, r11d
	mov r11d, r9d
	and r11d, eax
	add r10d, r11d
	ror r10d, 23
	add r10d, eax
	add r9d, DWORD PTR [rsi+28]
	add r9d, 1735328473
	mov r11d, r8d
	xor r11d, -1
	and r11d, eax
	add r9d, r11d
	mov r11d, r8d
	and r11d, r10d
	add r9d, r11d
	ror r9d, 18
	add r9d, r10d
	add r8d, DWORD PTR [rsi+48]
	add r8d, -1926607734
	mov r11d, eax
	xor r11d, -1
	and r11d, r10d
	add r8d, r11d
	mov r11d, eax
	and r11d, r9d
	add r8d, r11d
	ror r8d, 12
	add r8d, r9d
	add eax, DWORD PTR [rsi+20]
	add eax, -378558
	mov r11d, r9d
	xor r11d, r10d
	xor r11d, r8d
	add eax, r11d
	ror eax, 28
	add eax, r8d
	add r10d, DWORD PTR [rsi+32]
	add r10d, -2022574463
	mov r11d, r8d
	xor r11d, r9d
	xor r11d, eax
	add r10d, r11d
	ror r10d, 21
	add r10d, eax
	add r9d, DWORD PTR [rsi+44]
	add r9d, 1839030562
	mov r11d, eax
	xor r11d, r8d
	xor r11d, r10d
	add r9d, r11d
	ror r9d, 16
	add r9d, r10d
	add r8d, DWORD PTR [rsi+56]
	add r8d, -35309556
	mov r11d, r10d
	xor r11d, eax
	xor r11d, r9d
	add r8d, r11d
	ror r8d, 9
	add r8d, r9d
	add eax, DWORD PTR [rsi+4]
	add eax, -1530992060
	mov r11d, r9d
	xor r11d, r10d
	xor r11d, r8d
	add eax, r11d
	ror eax, 28
	add eax, r8d
	add r10d, DWORD PTR [rsi+16]
	add r10d, 1272893353
	mov r11d, r8d
	xor r11d, r9d
	xor r11d, eax
	add r10d, r11d
	ror r10d, 21
	add r10d, eax
	add r9d, DWORD PTR [rsi+28]
	add r9d, -155497632
	mov r11d, eax
	xor r11d, r8d
	xor r11d, r10d
	add r9d, r11d
	ror r9d, 16
	add r9d, r10d
	add r8d, DWORD PTR [rsi+40]
	add r8d, -1094730640
	mov r11d, r10d
	xor r11d, eax
	xor r11d, r9d
	add r8d, r11d
	ror r8d, 9
	add r8d, r9d
	add eax, DWORD PTR [rsi+52]
	add eax, 681279174
	mov r11d, r9d
	xor r11d, r10d
	xor r11d, r8d
	add eax, r11d
	ror eax, 28
	add eax, r8d
	add r10d, DWORD PTR [rsi]
	add r10d, -358537222
	mov r11d, r8d
	xor r11d, r9d
	xor r11d, eax
	add r10d, r11d
	ror r10d, 21
	add r10d, eax
	add r9d, DWORD PTR [rsi+12]
	add r9d, -722521979
	mov r11d, eax
	xor r11d, r8d
	xor r11d, r10d
	add r9d, r11d
	ror r9d, 16
	add r9d, r10d
	add r8d, DWORD PTR [rsi+24]
	add r8d, 76029189
	mov r11d, r10d
	xor r11d, eax
	xor r11d, r9d
	add r8d, r11d
	ror r8d, 9
	add r8d, r9d
	add eax, DWORD PTR [rsi+36]
	add eax, -640364487
	mov r11d, r9d
	xor r11d, r10d
	xor r11d, r8d
	add eax, r11d
	ror eax, 28
	add eax, r8d
	add r10d, DWORD PTR [rsi+48]
	add r10d, -421815835
	mov r11d, r8d
	xor r11d, r9d
	xor r11d, eax
	add r10d, r11d
	ror r10d, 21
	add r10d, eax
	add r9d, DWORD PTR [rsi+60]
	add r9d, 530742520
	mov r11d, eax
	xor r11d, r8d
	xor r11d, r10d
	add r9d, r11d
	ror r9d, 16
	add r9d, r10d
	add r8d, DWORD PTR [rsi+8]
	add r8d, -995338651
	mov r11d, r10d
	xor r11d, eax
	xor r11d, r9d
	add r8d, r11d
	ror r8d, 9
	add r8d, r9d
	add eax, DWORD PTR [rsi]
	add eax, -198630844
	mov r11d, r10d
	xor r11d, -1
	or r11d, r8d
	xor r11d, r9d
	add eax, r11d
	ror eax, 26
	add eax, r8d
	add r10d, DWORD PTR [rsi+28]
	add r10d, 1126891415
	mov r11d, r9d
	xor r11d, -1
	or r11d, eax
	xor r11d, r8d
	add r10d, r11d
	ror r10d, 22
	add r10d, eax
	add r9d, DWORD PTR [rsi+56]
	add r9d, -1416354905
	mov r11d, r8d
	xor r11d, -1
	or r11d, r10d
	xor r11d, eax
	add r9d, r11d
	ror r9d, 17
	add r9d, r10d
	add r8d, DWORD PTR [rsi+20]
	add r8d, -57434055
	mov r11d, eax
	xor r11d, -1
	or r11d, r9d
	xor r11d, r10d
	add r8d, r11d
	ror r8d, 11
	add r8d, r9d
	add eax, DWORD PTR [rsi+48]
	add eax, 1700485571
	mov r11d, r10d
	xor r11d, -1
	or r11d, r8d
	xor r11d, r9d
	add eax, r11d
	ror eax, 26
	add eax, r8d
	add r10d, DWORD PTR [rsi+12]
	add r10d, -1894986606
	mov r11d, r9d
	xor r11d, -1
	or r11d, eax
	xor r11d, r8d
	add r10d, r11d
	ror r10d, 22
	add r10d, eax
	add r9d, DWORD PTR [rsi+40]
	add r9d, -1051523
	mov r11d, r8d
	xor r11d, -1
	or r11d, r10d
	xor r11d, eax
	add r9d, r11d
	ror r9d, 17
	add r9d, r10d
	add r8d, DWORD PTR [rsi+4]
	add r8d, -2054922799
	mov r11d, eax
	xor r11d, -1
	or r11d, r9d
	xor r11d, r10d
	add r8d, r11d
	ror r8d, 11
	add r8d, r9d
	add eax, DWORD PTR [rsi+32]
	add eax, 1873313359
	mov r11d, r10d
	xor r11d, -1
	or r11d, r8d
	xor r11d, r9d
	add eax, r11d
	ror eax, 26
	add eax, r8d
	add r10d, DWORD PTR [rsi+60]
	add r10d, -30611744
	mov r11d, r9d
	xor r11d, -1
	or r11d, eax
	xor r11d, r8d
	add r10d, r11d
	ror r10d, 22
	add r10d, eax
	add r9d, DWORD PTR [rsi+24]
	add r9d, -1560198380
	mov r11d, r8d
	xor r11d, -1
	or r11d, r10d
	xor r11d, eax
	add r9d, r11d
	ror r9d, 17
	add r9d, r10d
	add r8d, DWORD PTR [rsi+52]
	add r8d, 1309151649
	mov r11d, eax
	xor r11d, -1
	or r11d, r9d
	xor r11d, r10d
	add r8d, r11d
	ror r8d, 11
	add r8d, r9d
	add eax, DWORD PTR [rsi+16]
	add eax, -145523070
	mov r11d, r10d
	xor r11d, -1
	or r11d, r8d
	xor r11d, r9d
	add eax, r11d
	ror eax, 26
	add eax, r8d
	add r10d, DWORD PTR [rsi+44]
	add r10d, -1120210379
	mov r11d, r9d
	xor r11d, -1
	or r11d, eax
	xor r11d, r8d
	add r10d, r11d
	ror r10d, 22
	add r10d, eax
	add r9d, DWORD PTR [rsi+8]
	add r9d, 718787259
	mov r11d, r8d
	xor r11d, -1
	or r11d, r10d
	xor r11d, eax
	add r9d, r11d
	ror r9d, 17
	add r9d, r10d
	add r8d, DWORD PTR [rsi+36]
	add r8d, -343485551
	mov r11d, eax
	xor r11d, -1
	or r11d, r9d
	xor r11d, r10d
	add r8d, r11d
	ror r8d, 11
	add r8d, r9d
	add eax, DWORD PTR [rdi]
	add r8d, DWORD PTR [rdi+4]
	add r9d, DWORD PTR [rdi+8]
	add r10d, DWORD PTR [rdi+12]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+4], r8d
	mov DWORD PTR [rdi+8], r9d
	mov DWORD PTR [rdi+12], r10d
	add rsi, 64
	sub rdx, 1
	jne 22b
	jmp 21f
20:
21:
	ret
	.p2align 6
