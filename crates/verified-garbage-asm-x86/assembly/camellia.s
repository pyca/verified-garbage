// The functions of `src/camellia.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_expand_key:
	lea esp, [esp-2708]
	mov eax, DWORD PTR [esp+2712]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2716]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2720]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+2592], ebx
	mov DWORD PTR [eax+2596], esi
	mov DWORD PTR [eax+2600], edi
	mov DWORD PTR [eax+2604], ebp
	mov edi, eax
	mov eax, -16777216
	mov DWORD PTR [edi+416], eax
	mov eax, -256
	mov DWORD PTR [edi+420], eax
	mov eax, -256
	mov DWORD PTR [edi+424], eax
	mov eax, -16711936
	mov DWORD PTR [edi+428], eax
	mov eax, -16711936
	mov DWORD PTR [edi+432], eax
	mov eax, -65281
	mov DWORD PTR [edi+436], eax
	mov eax, -65536
	mov DWORD PTR [edi+440], eax
	mov eax, 65535
	mov DWORD PTR [edi+444], eax
	mov eax, -16776961
	mov DWORD PTR [edi+448], eax
	mov eax, -16776961
	mov DWORD PTR [edi+452], eax
	mov eax, 65280
	mov DWORD PTR [edi+456], eax
	mov eax, -16711681
	mov DWORD PTR [edi+460], eax
	mov eax, 16711935
	mov DWORD PTR [edi+464], eax
	mov eax, 255
	mov DWORD PTR [edi+468], eax
	mov eax, 65280
	mov DWORD PTR [edi+472], eax
	mov eax, -256
	mov DWORD PTR [edi+476], eax
	mov eax, 0
	mov DWORD PTR [edi+480], eax
	mov eax, 65535
	mov DWORD PTR [edi+484], eax
	mov eax, 255
	mov DWORD PTR [edi+488], eax
	mov eax, -256
	mov DWORD PTR [edi+492], eax
	mov eax, -16711681
	mov DWORD PTR [edi+496], eax
	mov eax, 16777215
	mov DWORD PTR [edi+500], eax
	mov eax, -256
	mov DWORD PTR [edi+504], eax
	mov eax, 16711935
	mov DWORD PTR [edi+508], eax
	mov eax, 16711680
	mov DWORD PTR [edi+512], eax
	mov eax, -256
	mov DWORD PTR [edi+516], eax
	mov eax, 255
	mov DWORD PTR [edi+520], eax
	mov eax, 65535
	mov DWORD PTR [edi+524], eax
	mov eax, -65536
	mov DWORD PTR [edi+528], eax
	mov eax, -256
	mov DWORD PTR [edi+532], eax
	mov eax, 16711935
	mov DWORD PTR [edi+536], eax
	mov eax, -16711936
	mov DWORD PTR [edi+540], eax
	mov eax, -256
	mov DWORD PTR [edi+544], eax
	mov eax, -1
	mov DWORD PTR [edi+548], eax
	mov eax, -1
	mov DWORD PTR [edi+552], eax
	mov eax, -16711936
	mov DWORD PTR [edi+556], eax
	mov eax, 16711680
	mov DWORD PTR [edi+560], eax
	mov eax, -256
	mov DWORD PTR [edi+564], eax
	mov eax, 65535
	mov DWORD PTR [edi+568], eax
	mov eax, 65535
	mov DWORD PTR [edi+572], eax
	mov eax, 65535
	mov DWORD PTR [edi+576], eax
	mov eax, -256
	mov DWORD PTR [edi+580], eax
	mov eax, -16711936
	mov DWORD PTR [edi+584], eax
	mov eax, -16711681
	mov DWORD PTR [edi+588], eax
	mov eax, -16777216
	mov DWORD PTR [edi+592], eax
	mov eax, -16776961
	mov DWORD PTR [edi+596], eax
	mov eax, 65535
	mov DWORD PTR [edi+600], eax
	mov eax, -65281
	mov DWORD PTR [edi+604], eax
	mov eax, -256
	mov DWORD PTR [edi+608], eax
	mov eax, 16776960
	mov DWORD PTR [edi+612], eax
	mov eax, -16711681
	mov DWORD PTR [edi+616], eax
	mov eax, 65280
	mov DWORD PTR [edi+620], eax
	mov eax, 16777215
	mov DWORD PTR [edi+624], eax
	mov eax, -16711936
	mov DWORD PTR [edi+628], eax
	mov eax, 16777215
	mov DWORD PTR [edi+632], eax
	mov eax, -16711936
	mov DWORD PTR [edi+636], eax
	mov eax, 16777215
	mov DWORD PTR [edi+640], eax
	mov eax, 16776960
	mov DWORD PTR [edi+644], eax
	mov eax, -65536
	mov DWORD PTR [edi+648], eax
	mov eax, -65536
	mov DWORD PTR [edi+652], eax
	mov eax, -16711681
	mov DWORD PTR [edi+656], eax
	mov eax, 16711935
	mov DWORD PTR [edi+660], eax
	mov eax, 16777215
	mov DWORD PTR [edi+664], eax
	mov eax, 65535
	mov DWORD PTR [edi+668], eax
	mov eax, 16776960
	mov DWORD PTR [edi+672], eax
	mov eax, -65536
	mov DWORD PTR [edi+676], eax
	mov eax, 16776960
	mov DWORD PTR [edi+680], eax
	mov eax, -16777216
	mov DWORD PTR [edi+684], eax
	mov eax, -16776961
	mov DWORD PTR [edi+688], eax
	mov eax, -256
	mov DWORD PTR [edi+692], eax
	mov eax, -16711936
	mov DWORD PTR [edi+696], eax
	mov eax, -16711936
	mov DWORD PTR [edi+700], eax
	mov eax, -65536
	mov DWORD PTR [edi+704], eax
	mov eax, 255
	mov DWORD PTR [edi+708], eax
	mov eax, -65281
	mov DWORD PTR [edi+712], eax
	mov eax, -1
	mov DWORD PTR [edi+716], eax
	mov eax, -16776961
	mov DWORD PTR [edi+720], eax
	mov eax, 16776960
	mov DWORD PTR [edi+724], eax
	mov eax, 65535
	mov DWORD PTR [edi+728], eax
	mov eax, 255
	mov DWORD PTR [edi+732], eax
	mov eax, 0
	mov DWORD PTR [edi+736], eax
	mov eax, -16711936
	mov DWORD PTR [edi+740], eax
	mov eax, 65280
	mov DWORD PTR [edi+744], eax
	mov eax, 16711680
	mov DWORD PTR [edi+748], eax
	mov eax, 65535
	mov DWORD PTR [edi+752], eax
	mov eax, 255
	mov DWORD PTR [edi+756], eax
	mov eax, -16711936
	mov DWORD PTR [edi+760], eax
	mov eax, -65281
	mov DWORD PTR [edi+764], eax
	mov eax, -65281
	mov DWORD PTR [edi+768], eax
	mov eax, 65535
	mov DWORD PTR [edi+772], eax
	mov eax, -16711936
	mov DWORD PTR [edi+776], eax
	mov eax, -16777216
	mov DWORD PTR [edi+780], eax
	mov eax, -16776961
	mov DWORD PTR [edi+784], eax
	mov eax, -16711681
	mov DWORD PTR [edi+788], eax
	mov eax, -256
	mov DWORD PTR [edi+792], eax
	mov eax, -1
	mov DWORD PTR [edi+796], eax
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [esp+8]
	cmp eax, 16
	je 20f
	mov eax, DWORD PTR [ecx+16]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [ecx+20]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [esp+8]
	cmp eax, 24
	je 22f
	mov eax, DWORD PTR [ecx+24]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [ecx+28]
	mov DWORD PTR [edi+316], eax
	jmp 23f
22:
	mov eax, DWORD PTR [ecx+16]
	xor eax, -1
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [ecx+20]
	xor eax, -1
	mov DWORD PTR [edi+316], eax
23:
	jmp 21f
20:
	mov eax, 0
	mov DWORD PTR [edi+304], eax
	mov DWORD PTR [edi+308], eax
	mov DWORD PTR [edi+312], eax
	mov DWORD PTR [edi+316], eax
21:
	mov esi, edi
	add esi, 416
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+304]
	xor eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+308]
	xor eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+312]
	xor eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+316]
	xor eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+332], eax
	mov eax, 3
	mov DWORD PTR [edi+2616], eax
24:
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+188]
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+128]
	mov ebx, DWORD PTR [edi]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+224], eax
	xor ebx, DWORD PTR [edi+256]
	mov DWORD PTR [edi+256], ebx
	mov eax, DWORD PTR [edi+132]
	mov ebx, DWORD PTR [edi+4]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+228], eax
	xor ebx, DWORD PTR [edi+260]
	mov DWORD PTR [edi+260], ebx
	mov eax, DWORD PTR [edi+136]
	mov ebx, DWORD PTR [edi+8]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+232], eax
	xor ebx, DWORD PTR [edi+264]
	mov DWORD PTR [edi+264], ebx
	mov eax, DWORD PTR [edi+140]
	mov ebx, DWORD PTR [edi+12]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+236], eax
	xor ebx, DWORD PTR [edi+268]
	mov DWORD PTR [edi+268], ebx
	mov eax, DWORD PTR [edi+144]
	mov ebx, DWORD PTR [edi+16]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+240], eax
	xor ebx, DWORD PTR [edi+272]
	mov DWORD PTR [edi+272], ebx
	mov eax, DWORD PTR [edi+148]
	mov ebx, DWORD PTR [edi+20]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+244], eax
	xor ebx, DWORD PTR [edi+276]
	mov DWORD PTR [edi+276], ebx
	mov eax, DWORD PTR [edi+152]
	mov ebx, DWORD PTR [edi+24]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+248], eax
	xor ebx, DWORD PTR [edi+280]
	mov DWORD PTR [edi+280], ebx
	mov eax, DWORD PTR [edi+156]
	mov ebx, DWORD PTR [edi+28]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+252], eax
	xor ebx, DWORD PTR [edi+284]
	mov DWORD PTR [edi+284], ebx
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+128]
	mov ebx, DWORD PTR [edi]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+160], eax
	xor ebx, DWORD PTR [edi+192]
	mov DWORD PTR [edi+192], ebx
	mov eax, DWORD PTR [edi+132]
	mov ebx, DWORD PTR [edi+4]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+164], eax
	xor ebx, DWORD PTR [edi+196]
	mov DWORD PTR [edi+196], ebx
	mov eax, DWORD PTR [edi+136]
	mov ebx, DWORD PTR [edi+8]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+168], eax
	xor ebx, DWORD PTR [edi+200]
	mov DWORD PTR [edi+200], ebx
	mov eax, DWORD PTR [edi+140]
	mov ebx, DWORD PTR [edi+12]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+172], eax
	xor ebx, DWORD PTR [edi+204]
	mov DWORD PTR [edi+204], ebx
	mov eax, DWORD PTR [edi+144]
	mov ebx, DWORD PTR [edi+16]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+176], eax
	xor ebx, DWORD PTR [edi+208]
	mov DWORD PTR [edi+208], ebx
	mov eax, DWORD PTR [edi+148]
	mov ebx, DWORD PTR [edi+20]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+180], eax
	xor ebx, DWORD PTR [edi+212]
	mov DWORD PTR [edi+212], ebx
	mov eax, DWORD PTR [edi+152]
	mov ebx, DWORD PTR [edi+24]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+184], eax
	xor ebx, DWORD PTR [edi+216]
	mov DWORD PTR [edi+216], ebx
	mov eax, DWORD PTR [edi+156]
	mov ebx, DWORD PTR [edi+28]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+188], eax
	xor ebx, DWORD PTR [edi+220]
	mov DWORD PTR [edi+220], ebx
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+332], eax
	add esi, 128
	mov eax, DWORD PTR [edi+2616]
	mov ebx, eax
	shr ebx, 1
	cmp ebx, 0
	jne 25f
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+364], eax
	jmp 26f
25:
	cmp eax, 3
	je 27f
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+304]
	xor eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+308]
	xor eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+312]
	xor eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+316]
	xor eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+332], eax
	jmp 28f
27:
	mov eax, DWORD PTR [edi+288]
	xor eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+292]
	xor eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+296]
	xor eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+300]
	xor eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+332], eax
28:
26:
	mov eax, DWORD PTR [edi+2616]
	sub eax, 1
	mov DWORD PTR [edi+2616], eax
	jne 24b
	mov eax, DWORD PTR [edi+288]
	bswap eax
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	bswap eax
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	bswap eax
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	bswap eax
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+304]
	bswap eax
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+308]
	bswap eax
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+312]
	bswap eax
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+316]
	bswap eax
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+336]
	bswap eax
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+340]
	bswap eax
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+344]
	bswap eax
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+348]
	bswap eax
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+352]
	bswap eax
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+356]
	bswap eax
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+360]
	bswap eax
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+364]
	bswap eax
	mov DWORD PTR [edi+364], eax
	mov edx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esp+8]
	cmp eax, 16
	je 29f
	mov eax, DWORD PTR [edi+288]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [edi+292]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [edi+296]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [edi+300]
	bswap eax
	mov DWORD PTR [edx+12], eax
	mov eax, DWORD PTR [edi+352]
	bswap eax
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [edi+356]
	bswap eax
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [edi+360]
	bswap eax
	mov DWORD PTR [edx+24], eax
	mov eax, DWORD PTR [edi+364]
	bswap eax
	mov DWORD PTR [edx+28], eax
	mov eax, DWORD PTR [edi+304]
	mov ebx, DWORD PTR [edi+308]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+32], eax
	mov eax, DWORD PTR [edi+308]
	mov ebx, DWORD PTR [edi+312]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+36], eax
	mov eax, DWORD PTR [edi+312]
	mov ebx, DWORD PTR [edi+316]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+40], eax
	mov eax, DWORD PTR [edi+316]
	mov ebx, DWORD PTR [edi+304]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+44], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+48], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+52], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+56], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+60], eax
	mov eax, DWORD PTR [edi+304]
	mov ebx, DWORD PTR [edi+308]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+64], eax
	mov eax, DWORD PTR [edi+308]
	mov ebx, DWORD PTR [edi+312]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+68], eax
	mov eax, DWORD PTR [edi+312]
	mov ebx, DWORD PTR [edi+316]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+72], eax
	mov eax, DWORD PTR [edi+316]
	mov ebx, DWORD PTR [edi+304]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+76], eax
	mov eax, DWORD PTR [edi+352]
	mov ebx, DWORD PTR [edi+356]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+80], eax
	mov eax, DWORD PTR [edi+356]
	mov ebx, DWORD PTR [edi+360]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+84], eax
	mov eax, DWORD PTR [edi+360]
	mov ebx, DWORD PTR [edi+364]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+88], eax
	mov eax, DWORD PTR [edi+364]
	mov ebx, DWORD PTR [edi+352]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+92], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+96], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+100], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+104], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+108], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+112], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+116], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+120], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+124], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+128], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+132], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+136], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+140], eax
	mov eax, DWORD PTR [edi+308]
	mov ebx, DWORD PTR [edi+312]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+144], eax
	mov eax, DWORD PTR [edi+312]
	mov ebx, DWORD PTR [edi+316]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+148], eax
	mov eax, DWORD PTR [edi+316]
	mov ebx, DWORD PTR [edi+304]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+152], eax
	mov eax, DWORD PTR [edi+304]
	mov ebx, DWORD PTR [edi+308]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+156], eax
	mov eax, DWORD PTR [edi+356]
	mov ebx, DWORD PTR [edi+360]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+160], eax
	mov eax, DWORD PTR [edi+360]
	mov ebx, DWORD PTR [edi+364]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+164], eax
	mov eax, DWORD PTR [edi+364]
	mov ebx, DWORD PTR [edi+352]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+168], eax
	mov eax, DWORD PTR [edi+352]
	mov ebx, DWORD PTR [edi+356]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+172], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+176], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+180], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+184], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+188], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+192], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+196], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+200], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+204], eax
	mov eax, DWORD PTR [edi+312]
	mov ebx, DWORD PTR [edi+316]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+208], eax
	mov eax, DWORD PTR [edi+316]
	mov ebx, DWORD PTR [edi+304]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+212], eax
	mov eax, DWORD PTR [edi+304]
	mov ebx, DWORD PTR [edi+308]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+216], eax
	mov eax, DWORD PTR [edi+308]
	mov ebx, DWORD PTR [edi+312]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+220], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+224], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+228], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+232], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+236], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+240], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+244], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+248], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+252], eax
	mov eax, DWORD PTR [edi+364]
	mov ebx, DWORD PTR [edi+352]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+256], eax
	mov eax, DWORD PTR [edi+352]
	mov ebx, DWORD PTR [edi+356]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+260], eax
	mov eax, DWORD PTR [edi+356]
	mov ebx, DWORD PTR [edi+360]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+264], eax
	mov eax, DWORD PTR [edi+360]
	mov ebx, DWORD PTR [edi+364]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+268], eax
	jmp 210f
29:
	mov eax, DWORD PTR [edi+288]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [edi+292]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [edi+296]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [edi+300]
	bswap eax
	mov DWORD PTR [edx+12], eax
	mov eax, DWORD PTR [edi+336]
	bswap eax
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [edi+340]
	bswap eax
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [edi+344]
	bswap eax
	mov DWORD PTR [edx+24], eax
	mov eax, DWORD PTR [edi+348]
	bswap eax
	mov DWORD PTR [edx+28], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+32], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+36], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+40], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+44], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+48], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+52], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+56], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+60], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+64], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+68], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+72], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+76], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+80], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+84], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+88], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+92], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+96], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+100], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+104], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+108], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+112], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+116], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+120], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+124], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+128], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+132], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+136], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+140], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+144], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+148], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+152], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+156], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+160], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+164], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+168], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+172], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+176], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+180], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+184], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+188], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+192], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+196], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+200], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+204], eax
210:
	mov ebx, DWORD PTR [edi+2592]
	mov esi, DWORD PTR [edi+2596]
	mov ebp, DWORD PTR [edi+2604]
	mov edi, DWORD PTR [edi+2600]
	mov ecx, 0
	mov DWORD PTR [esp+20], ecx
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
	lea esp, [esp+2708]
	ret
	.p2align 6

vg_camellia_ecb_encrypt:
	lea esp, [esp-2712]
	mov eax, DWORD PTR [esp+2716]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2720]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2724]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2728]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+2592], ebx
	mov DWORD PTR [eax+2596], esi
	mov DWORD PTR [eax+2600], edi
	mov DWORD PTR [eax+2604], ebp
	mov edi, eax
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
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+2612], eax
	test eax, eax
	je 24f
26:
	mov esi, DWORD PTR [edi+2608]
	mov ebp, DWORD PTR [edi+2612]
	mov ecx, ebp
	cmp ebp, 8
	jb 27f
	mov ecx, 8
	jmp 28f
27:
28:
	mov edx, esi
	mov ebx, edi
	add ebx, 288
29:
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebx+12], eax
	add edx, 16
	add ebx, 16
	sub ecx, 1
	jne 29b
	mov DWORD PTR [edi+2608], esi
	mov DWORD PTR [edi+2612], ebp
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
	mov esi, DWORD PTR [edi+2608]
	mov ebp, DWORD PTR [edi+2612]
	mov ecx, ebp
	cmp ebp, 8
	jb 210f
	mov ecx, 8
	jmp 211f
210:
211:
	mov edx, edi
	add edx, 288
	mov ebx, esi
212:
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebx+12], eax
	add edx, 16
	add ebx, 16
	sub ecx, 1
	jne 212b
	mov ecx, ebp
	cmp ebp, 8
	jb 213f
	mov ecx, 8
	jmp 214f
213:
214:
	add esi, 128
	sub ebp, ecx
	mov DWORD PTR [edi+2608], esi
	mov DWORD PTR [edi+2612], ebp
	jne 26b
	jmp 25f
24:
25:
	mov ebx, DWORD PTR [edi+2592]
	mov esi, DWORD PTR [edi+2596]
	mov ebp, DWORD PTR [edi+2604]
	mov edi, DWORD PTR [edi+2600]
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
	lea esp, [esp+2712]
	ret
	.p2align 6

vg_camellia_ecb_decrypt:
	lea esp, [esp-2712]
	mov eax, DWORD PTR [esp+2716]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2720]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2724]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2728]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+2592], ebx
	mov DWORD PTR [eax+2596], esi
	mov DWORD PTR [eax+2600], edi
	mov DWORD PTR [eax+2604], ebp
	mov edi, eax
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
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+2612], eax
	test eax, eax
	je 24f
26:
	mov esi, DWORD PTR [edi+2608]
	mov ebp, DWORD PTR [edi+2612]
	mov ecx, ebp
	cmp ebp, 8
	jb 27f
	mov ecx, 8
	jmp 28f
27:
28:
	mov edx, esi
	mov ebx, edi
	add ebx, 288
29:
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebx+12], eax
	add edx, 16
	add ebx, 16
	sub ecx, 1
	jne 29b
	mov DWORD PTR [edi+2608], esi
	mov DWORD PTR [edi+2612], ebp
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
	mov esi, DWORD PTR [edi+2608]
	mov ebp, DWORD PTR [edi+2612]
	mov ecx, ebp
	cmp ebp, 8
	jb 210f
	mov ecx, 8
	jmp 211f
210:
211:
	mov edx, edi
	add edx, 288
	mov ebx, esi
212:
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebx+12], eax
	add edx, 16
	add ebx, 16
	sub ecx, 1
	jne 212b
	mov ecx, ebp
	cmp ebp, 8
	jb 213f
	mov ecx, 8
	jmp 214f
213:
214:
	add esi, 128
	sub ebp, ecx
	mov DWORD PTR [edi+2608], esi
	mov DWORD PTR [edi+2612], ebp
	jne 26b
	jmp 25f
24:
25:
	mov ebx, DWORD PTR [edi+2592]
	mov esi, DWORD PTR [edi+2596]
	mov ebp, DWORD PTR [edi+2604]
	mov edi, DWORD PTR [edi+2600]
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
	lea esp, [esp+2712]
	ret
	.p2align 6

vg_camellia_crypt_prepared:
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [eax+2620], ebx
	mov DWORD PTR [eax+2624], esi
	mov DWORD PTR [eax+2628], edi
	mov DWORD PTR [eax+2632], ebp
	mov edi, eax
	mov eax, DWORD PTR [esp+4]
	cmp eax, 18
	je 20f
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+284], eax
	mov esi, edi
	add esi, 416
	mov eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+188]
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+284], eax
	add esi, 128
22:
	mov eax, esi
	add eax, 384
	mov DWORD PTR [edi+2616], eax
23:
	mov eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+188]
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+128]
	mov ebx, DWORD PTR [edi]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+224], eax
	xor ebx, DWORD PTR [edi+256]
	mov DWORD PTR [edi+256], ebx
	mov eax, DWORD PTR [edi+132]
	mov ebx, DWORD PTR [edi+4]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+228], eax
	xor ebx, DWORD PTR [edi+260]
	mov DWORD PTR [edi+260], ebx
	mov eax, DWORD PTR [edi+136]
	mov ebx, DWORD PTR [edi+8]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+232], eax
	xor ebx, DWORD PTR [edi+264]
	mov DWORD PTR [edi+264], ebx
	mov eax, DWORD PTR [edi+140]
	mov ebx, DWORD PTR [edi+12]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+236], eax
	xor ebx, DWORD PTR [edi+268]
	mov DWORD PTR [edi+268], ebx
	mov eax, DWORD PTR [edi+144]
	mov ebx, DWORD PTR [edi+16]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+240], eax
	xor ebx, DWORD PTR [edi+272]
	mov DWORD PTR [edi+272], ebx
	mov eax, DWORD PTR [edi+148]
	mov ebx, DWORD PTR [edi+20]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+244], eax
	xor ebx, DWORD PTR [edi+276]
	mov DWORD PTR [edi+276], ebx
	mov eax, DWORD PTR [edi+152]
	mov ebx, DWORD PTR [edi+24]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+248], eax
	xor ebx, DWORD PTR [edi+280]
	mov DWORD PTR [edi+280], ebx
	mov eax, DWORD PTR [edi+156]
	mov ebx, DWORD PTR [edi+28]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+252], eax
	xor ebx, DWORD PTR [edi+284]
	mov DWORD PTR [edi+284], ebx
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+128]
	mov ebx, DWORD PTR [edi]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+160], eax
	xor ebx, DWORD PTR [edi+192]
	mov DWORD PTR [edi+192], ebx
	mov eax, DWORD PTR [edi+132]
	mov ebx, DWORD PTR [edi+4]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+164], eax
	xor ebx, DWORD PTR [edi+196]
	mov DWORD PTR [edi+196], ebx
	mov eax, DWORD PTR [edi+136]
	mov ebx, DWORD PTR [edi+8]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+168], eax
	xor ebx, DWORD PTR [edi+200]
	mov DWORD PTR [edi+200], ebx
	mov eax, DWORD PTR [edi+140]
	mov ebx, DWORD PTR [edi+12]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+172], eax
	xor ebx, DWORD PTR [edi+204]
	mov DWORD PTR [edi+204], ebx
	mov eax, DWORD PTR [edi+144]
	mov ebx, DWORD PTR [edi+16]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+176], eax
	xor ebx, DWORD PTR [edi+208]
	mov DWORD PTR [edi+208], ebx
	mov eax, DWORD PTR [edi+148]
	mov ebx, DWORD PTR [edi+20]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+180], eax
	xor ebx, DWORD PTR [edi+212]
	mov DWORD PTR [edi+212], ebx
	mov eax, DWORD PTR [edi+152]
	mov ebx, DWORD PTR [edi+24]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+184], eax
	xor ebx, DWORD PTR [edi+216]
	mov DWORD PTR [edi+216], ebx
	mov eax, DWORD PTR [edi+156]
	mov ebx, DWORD PTR [edi+28]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+188], eax
	xor ebx, DWORD PTR [edi+220]
	mov DWORD PTR [edi+220], ebx
	add esi, 128
	mov eax, DWORD PTR [edi+2616]
	cmp eax, esi
	jne 23b
	mov eax, esi
	sub eax, edi
	cmp eax, 2464
	jne 24f
	jmp 25f
24:
	mov eax, DWORD PTR [esi+96]
	or eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [esi+100]
	or eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [esi+104]
	or eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [esi+108]
	or eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [esi+112]
	or eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [esi+116]
	or eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [esi+120]
	or eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [esi+124]
	or eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [esi+92]
	and eax, DWORD PTR [edi+252]
	ror eax, 8
	xor eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [esi+64]
	and eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [esi+68]
	and eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [esi+72]
	and eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [esi+76]
	and eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [esi+80]
	and eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [esi+84]
	and eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [esi+88]
	and eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [esi+28]
	and eax, DWORD PTR [edi+188]
	ror eax, 8
	xor eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [esi+8]
	and eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [esi+12]
	and eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [esi+20]
	and eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [esi+24]
	and eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [esi+32]
	or eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [esi+36]
	or eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [esi+40]
	or eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [esi+44]
	or eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [esi+48]
	or eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [esi+52]
	or eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [esi+56]
	or eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [esi+60]
	or eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+188], eax
	add esi, 128
25:
	mov eax, esi
	sub eax, edi
	cmp eax, 2464
	jne 22b
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+188]
	xor eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+412], eax
	jmp 21f
20:
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+284], eax
	mov esi, edi
	add esi, 416
	mov eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+188]
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+284], eax
	add esi, 128
26:
	mov eax, esi
	add eax, 384
	mov DWORD PTR [edi+2616], eax
27:
	mov eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+188]
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+128]
	mov ebx, DWORD PTR [edi]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+224], eax
	xor ebx, DWORD PTR [edi+256]
	mov DWORD PTR [edi+256], ebx
	mov eax, DWORD PTR [edi+132]
	mov ebx, DWORD PTR [edi+4]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+228], eax
	xor ebx, DWORD PTR [edi+260]
	mov DWORD PTR [edi+260], ebx
	mov eax, DWORD PTR [edi+136]
	mov ebx, DWORD PTR [edi+8]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+232], eax
	xor ebx, DWORD PTR [edi+264]
	mov DWORD PTR [edi+264], ebx
	mov eax, DWORD PTR [edi+140]
	mov ebx, DWORD PTR [edi+12]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+236], eax
	xor ebx, DWORD PTR [edi+268]
	mov DWORD PTR [edi+268], ebx
	mov eax, DWORD PTR [edi+144]
	mov ebx, DWORD PTR [edi+16]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+240], eax
	xor ebx, DWORD PTR [edi+272]
	mov DWORD PTR [edi+272], ebx
	mov eax, DWORD PTR [edi+148]
	mov ebx, DWORD PTR [edi+20]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+244], eax
	xor ebx, DWORD PTR [edi+276]
	mov DWORD PTR [edi+276], ebx
	mov eax, DWORD PTR [edi+152]
	mov ebx, DWORD PTR [edi+24]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+248], eax
	xor ebx, DWORD PTR [edi+280]
	mov DWORD PTR [edi+280], ebx
	mov eax, DWORD PTR [edi+156]
	mov ebx, DWORD PTR [edi+28]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+252], eax
	xor ebx, DWORD PTR [edi+284]
	mov DWORD PTR [edi+284], ebx
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+128]
	mov ebx, DWORD PTR [edi]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+160], eax
	xor ebx, DWORD PTR [edi+192]
	mov DWORD PTR [edi+192], ebx
	mov eax, DWORD PTR [edi+132]
	mov ebx, DWORD PTR [edi+4]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+164], eax
	xor ebx, DWORD PTR [edi+196]
	mov DWORD PTR [edi+196], ebx
	mov eax, DWORD PTR [edi+136]
	mov ebx, DWORD PTR [edi+8]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+168], eax
	xor ebx, DWORD PTR [edi+200]
	mov DWORD PTR [edi+200], ebx
	mov eax, DWORD PTR [edi+140]
	mov ebx, DWORD PTR [edi+12]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+172], eax
	xor ebx, DWORD PTR [edi+204]
	mov DWORD PTR [edi+204], ebx
	mov eax, DWORD PTR [edi+144]
	mov ebx, DWORD PTR [edi+16]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+176], eax
	xor ebx, DWORD PTR [edi+208]
	mov DWORD PTR [edi+208], ebx
	mov eax, DWORD PTR [edi+148]
	mov ebx, DWORD PTR [edi+20]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+180], eax
	xor ebx, DWORD PTR [edi+212]
	mov DWORD PTR [edi+212], ebx
	mov eax, DWORD PTR [edi+152]
	mov ebx, DWORD PTR [edi+24]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+184], eax
	xor ebx, DWORD PTR [edi+216]
	mov DWORD PTR [edi+216], ebx
	mov eax, DWORD PTR [edi+156]
	mov ebx, DWORD PTR [edi+28]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+188], eax
	xor ebx, DWORD PTR [edi+220]
	mov DWORD PTR [edi+220], ebx
	add esi, 128
	mov eax, DWORD PTR [edi+2616]
	cmp eax, esi
	jne 27b
	mov eax, esi
	sub eax, edi
	cmp eax, 1952
	jne 28f
	jmp 29f
28:
	mov eax, DWORD PTR [esi+96]
	or eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [esi+100]
	or eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [esi+104]
	or eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [esi+108]
	or eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [esi+112]
	or eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [esi+116]
	or eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [esi+120]
	or eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [esi+124]
	or eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [esi+92]
	and eax, DWORD PTR [edi+252]
	ror eax, 8
	xor eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [esi+64]
	and eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [esi+68]
	and eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [esi+72]
	and eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [esi+76]
	and eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [esi+80]
	and eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [esi+84]
	and eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [esi+88]
	and eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [esi+28]
	and eax, DWORD PTR [edi+188]
	ror eax, 8
	xor eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [esi+8]
	and eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [esi+12]
	and eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [esi+20]
	and eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [esi+24]
	and eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [esi+32]
	or eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [esi+36]
	or eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [esi+40]
	or eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [esi+44]
	or eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [esi+48]
	or eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [esi+52]
	or eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [esi+56]
	or eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [esi+60]
	or eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+188], eax
	add esi, 128
29:
	mov eax, esi
	sub eax, edi
	cmp eax, 1952
	jne 26b
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+188]
	xor eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+412], eax
21:
	mov ebx, DWORD PTR [edi+2620]
	mov esi, DWORD PTR [edi+2624]
	mov ebp, DWORD PTR [edi+2632]
	mov edi, DWORD PTR [edi+2628]
	ret
	.p2align 6
