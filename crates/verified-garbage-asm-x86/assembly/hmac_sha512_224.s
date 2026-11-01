// The functions of `src/hmac_sha512_224.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha512_224_init:
	mov eax, DWORD PTR [esp+16]
	cmp eax, 129
	jae 20f
	lea esp, [esp-1896]
	mov eax, DWORD PTR [esp+1900]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1904]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1908]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1912]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+272], ebx
	mov DWORD PTR [eax+276], esi
	mov DWORD PTR [eax+280], edi
	mov DWORD PTR [eax+284], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	push ebx
	call {vg_sha512_224_init}
	pop eax
	push esi
	call {vg_sha512_224_init}
	pop eax
	mov ecx, 909522486
	mov DWORD PTR [ebx+64], ecx
	mov DWORD PTR [ebx+68], ecx
	mov DWORD PTR [ebx+72], ecx
	mov DWORD PTR [ebx+76], ecx
	mov DWORD PTR [ebx+80], ecx
	mov DWORD PTR [ebx+84], ecx
	mov DWORD PTR [ebx+88], ecx
	mov DWORD PTR [ebx+92], ecx
	mov DWORD PTR [ebx+96], ecx
	mov DWORD PTR [ebx+100], ecx
	mov DWORD PTR [ebx+104], ecx
	mov DWORD PTR [ebx+108], ecx
	mov DWORD PTR [ebx+112], ecx
	mov DWORD PTR [ebx+116], ecx
	mov DWORD PTR [ebx+120], ecx
	mov DWORD PTR [ebx+124], ecx
	mov DWORD PTR [ebx+128], ecx
	mov DWORD PTR [ebx+132], ecx
	mov DWORD PTR [ebx+136], ecx
	mov DWORD PTR [ebx+140], ecx
	mov DWORD PTR [ebx+144], ecx
	mov DWORD PTR [ebx+148], ecx
	mov DWORD PTR [ebx+152], ecx
	mov DWORD PTR [ebx+156], ecx
	mov DWORD PTR [ebx+160], ecx
	mov DWORD PTR [ebx+164], ecx
	mov DWORD PTR [ebx+168], ecx
	mov DWORD PTR [ebx+172], ecx
	mov DWORD PTR [ebx+176], ecx
	mov DWORD PTR [ebx+180], ecx
	mov DWORD PTR [ebx+184], ecx
	mov DWORD PTR [ebx+188], ecx
	mov edi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, ebx
	add edx, 64
	test ecx, ecx
	je 22f
24:
	movzx eax, BYTE PTR [edi]
	xor eax, 54
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 24b
	jmp 23f
22:
23:
	mov eax, DWORD PTR [ebx+64]
	xor eax, 1785358954
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [ebx+68]
	xor eax, 1785358954
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [ebx+72]
	xor eax, 1785358954
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [ebx+76]
	xor eax, 1785358954
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [ebx+80]
	xor eax, 1785358954
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [ebx+84]
	xor eax, 1785358954
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [ebx+88]
	xor eax, 1785358954
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [ebx+92]
	xor eax, 1785358954
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [ebx+96]
	xor eax, 1785358954
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [ebx+100]
	xor eax, 1785358954
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [ebx+104]
	xor eax, 1785358954
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [ebx+108]
	xor eax, 1785358954
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [ebx+112]
	xor eax, 1785358954
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [ebx+116]
	xor eax, 1785358954
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [ebx+120]
	xor eax, 1785358954
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [ebx+124]
	xor eax, 1785358954
	mov DWORD PTR [esi+124], eax
	mov eax, DWORD PTR [ebx+128]
	xor eax, 1785358954
	mov DWORD PTR [esi+128], eax
	mov eax, DWORD PTR [ebx+132]
	xor eax, 1785358954
	mov DWORD PTR [esi+132], eax
	mov eax, DWORD PTR [ebx+136]
	xor eax, 1785358954
	mov DWORD PTR [esi+136], eax
	mov eax, DWORD PTR [ebx+140]
	xor eax, 1785358954
	mov DWORD PTR [esi+140], eax
	mov eax, DWORD PTR [ebx+144]
	xor eax, 1785358954
	mov DWORD PTR [esi+144], eax
	mov eax, DWORD PTR [ebx+148]
	xor eax, 1785358954
	mov DWORD PTR [esi+148], eax
	mov eax, DWORD PTR [ebx+152]
	xor eax, 1785358954
	mov DWORD PTR [esi+152], eax
	mov eax, DWORD PTR [ebx+156]
	xor eax, 1785358954
	mov DWORD PTR [esi+156], eax
	mov eax, DWORD PTR [ebx+160]
	xor eax, 1785358954
	mov DWORD PTR [esi+160], eax
	mov eax, DWORD PTR [ebx+164]
	xor eax, 1785358954
	mov DWORD PTR [esi+164], eax
	mov eax, DWORD PTR [ebx+168]
	xor eax, 1785358954
	mov DWORD PTR [esi+168], eax
	mov eax, DWORD PTR [ebx+172]
	xor eax, 1785358954
	mov DWORD PTR [esi+172], eax
	mov eax, DWORD PTR [ebx+176]
	xor eax, 1785358954
	mov DWORD PTR [esi+176], eax
	mov eax, DWORD PTR [ebx+180]
	xor eax, 1785358954
	mov DWORD PTR [esi+180], eax
	mov eax, DWORD PTR [ebx+184]
	xor eax, 1785358954
	mov DWORD PTR [esi+184], eax
	mov eax, DWORD PTR [ebx+188]
	xor eax, 1785358954
	mov DWORD PTR [esi+188], eax
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, esi
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	mov ebx, DWORD PTR [eax+272]
	mov esi, DWORD PTR [eax+276]
	mov edi, DWORD PTR [eax+280]
	mov ebp, DWORD PTR [eax+284]
	lea esp, [esp+1896]
21:
	ret
20:
	lea esp, [esp-3432]
	mov eax, DWORD PTR [esp+3436]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+3440]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+3444]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+3448]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+1872], ebx
	mov DWORD PTR [eax+1876], esi
	mov DWORD PTR [eax+1880], edi
	mov DWORD PTR [eax+1884], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+16]
	cmp ecx, 129
	jae 25f
	mov edx, DWORD PTR [esp+12]
	jmp 26f
25:
	mov edi, ebp
	add edi, 2464
	push edi
	call {vg_sha512_224_init}
	pop eax
	mov eax, 0
	mov esi, 0
	mov ecx, DWORD PTR [esp+16]
	mov edx, DWORD PTR [esp+12]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha512_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+16]
	mov ecx, 0
	mov edx, ebp
	add edx, 2712
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 2712
	mov ecx, 28
26:
	mov edi, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha512_224_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	mov ebx, DWORD PTR [eax+1872]
	mov esi, DWORD PTR [eax+1876]
	mov edi, DWORD PTR [eax+1880]
	mov ebp, DWORD PTR [eax+1884]
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
	mov DWORD PTR [esp+2756], ecx
	mov DWORD PTR [esp+2760], ecx
	mov DWORD PTR [esp+2764], ecx
	mov DWORD PTR [esp+2768], ecx
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
	mov DWORD PTR [esp+2824], ecx
	mov DWORD PTR [esp+2828], ecx
	mov DWORD PTR [esp+2832], ecx
	mov DWORD PTR [esp+2836], ecx
	mov DWORD PTR [esp+2840], ecx
	mov DWORD PTR [esp+2844], ecx
	mov DWORD PTR [esp+2848], ecx
	mov DWORD PTR [esp+2852], ecx
	mov DWORD PTR [esp+2856], ecx
	mov DWORD PTR [esp+2860], ecx
	mov DWORD PTR [esp+2864], ecx
	mov DWORD PTR [esp+2868], ecx
	mov DWORD PTR [esp+2872], ecx
	mov DWORD PTR [esp+2876], ecx
	mov DWORD PTR [esp+2880], ecx
	mov DWORD PTR [esp+2884], ecx
	mov DWORD PTR [esp+2888], ecx
	mov DWORD PTR [esp+2892], ecx
	mov DWORD PTR [esp+2896], ecx
	mov DWORD PTR [esp+2900], ecx
	mov DWORD PTR [esp+2904], ecx
	mov DWORD PTR [esp+2908], ecx
	mov DWORD PTR [esp+2912], ecx
	mov DWORD PTR [esp+2916], ecx
	mov DWORD PTR [esp+2920], ecx
	mov DWORD PTR [esp+2924], ecx
	mov DWORD PTR [esp+2928], ecx
	mov DWORD PTR [esp+2932], ecx
	mov DWORD PTR [esp+2936], ecx
	mov DWORD PTR [esp+2940], ecx
	mov DWORD PTR [esp+2944], ecx
	mov DWORD PTR [esp+2948], ecx
	mov DWORD PTR [esp+2952], ecx
	mov DWORD PTR [esp+2956], ecx
	mov DWORD PTR [esp+2960], ecx
	mov DWORD PTR [esp+2964], ecx
	mov DWORD PTR [esp+2968], ecx
	mov DWORD PTR [esp+2972], ecx
	mov DWORD PTR [esp+2976], ecx
	mov DWORD PTR [esp+2980], ecx
	mov DWORD PTR [esp+2984], ecx
	mov DWORD PTR [esp+2988], ecx
	mov DWORD PTR [esp+2992], ecx
	mov DWORD PTR [esp+2996], ecx
	mov DWORD PTR [esp+3000], ecx
	mov DWORD PTR [esp+3004], ecx
	mov DWORD PTR [esp+3008], ecx
	mov DWORD PTR [esp+3012], ecx
	mov DWORD PTR [esp+3016], ecx
	mov DWORD PTR [esp+3020], ecx
	mov DWORD PTR [esp+3024], ecx
	mov DWORD PTR [esp+3028], ecx
	mov DWORD PTR [esp+3032], ecx
	mov DWORD PTR [esp+3036], ecx
	mov DWORD PTR [esp+3040], ecx
	mov DWORD PTR [esp+3044], ecx
	mov DWORD PTR [esp+3048], ecx
	mov DWORD PTR [esp+3052], ecx
	mov DWORD PTR [esp+3056], ecx
	mov DWORD PTR [esp+3060], ecx
	mov DWORD PTR [esp+3064], ecx
	mov DWORD PTR [esp+3068], ecx
	mov DWORD PTR [esp+3072], ecx
	mov DWORD PTR [esp+3076], ecx
	mov DWORD PTR [esp+3080], ecx
	mov DWORD PTR [esp+3084], ecx
	mov DWORD PTR [esp+3088], ecx
	mov DWORD PTR [esp+3092], ecx
	mov DWORD PTR [esp+3096], ecx
	mov DWORD PTR [esp+3100], ecx
	mov DWORD PTR [esp+3104], ecx
	mov DWORD PTR [esp+3108], ecx
	mov DWORD PTR [esp+3112], ecx
	mov DWORD PTR [esp+3116], ecx
	mov DWORD PTR [esp+3120], ecx
	mov DWORD PTR [esp+3124], ecx
	mov DWORD PTR [esp+3128], ecx
	mov DWORD PTR [esp+3132], ecx
	mov DWORD PTR [esp+3136], ecx
	mov DWORD PTR [esp+3140], ecx
	mov DWORD PTR [esp+3144], ecx
	mov DWORD PTR [esp+3148], ecx
	mov DWORD PTR [esp+3152], ecx
	mov DWORD PTR [esp+3156], ecx
	mov DWORD PTR [esp+3160], ecx
	mov DWORD PTR [esp+3164], ecx
	mov DWORD PTR [esp+3168], ecx
	mov DWORD PTR [esp+3172], ecx
	mov DWORD PTR [esp+3176], ecx
	mov DWORD PTR [esp+3180], ecx
	mov DWORD PTR [esp+3184], ecx
	mov DWORD PTR [esp+3188], ecx
	mov DWORD PTR [esp+3192], ecx
	mov DWORD PTR [esp+3196], ecx
	mov DWORD PTR [esp+3200], ecx
	mov DWORD PTR [esp+3204], ecx
	mov DWORD PTR [esp+3208], ecx
	mov DWORD PTR [esp+3212], ecx
	mov DWORD PTR [esp+3216], ecx
	mov DWORD PTR [esp+3220], ecx
	mov DWORD PTR [esp+3224], ecx
	mov DWORD PTR [esp+3228], ecx
	mov DWORD PTR [esp+3232], ecx
	mov DWORD PTR [esp+3236], ecx
	mov DWORD PTR [esp+3240], ecx
	mov DWORD PTR [esp+3244], ecx
	mov DWORD PTR [esp+3248], ecx
	mov DWORD PTR [esp+3252], ecx
	mov DWORD PTR [esp+3256], ecx
	mov DWORD PTR [esp+3260], ecx
	mov DWORD PTR [esp+3264], ecx
	mov DWORD PTR [esp+3268], ecx
	mov DWORD PTR [esp+3272], ecx
	mov DWORD PTR [esp+3276], ecx
	mov DWORD PTR [esp+3280], ecx
	mov DWORD PTR [esp+3284], ecx
	mov DWORD PTR [esp+3288], ecx
	mov DWORD PTR [esp+3292], ecx
	mov DWORD PTR [esp+3296], ecx
	mov DWORD PTR [esp+3300], ecx
	mov DWORD PTR [esp+3304], ecx
	mov DWORD PTR [esp+3308], ecx
	mov DWORD PTR [esp+3312], ecx
	mov DWORD PTR [esp+3316], ecx
	mov DWORD PTR [esp+3320], ecx
	mov DWORD PTR [esp+3324], ecx
	mov DWORD PTR [esp+3328], ecx
	mov DWORD PTR [esp+3332], ecx
	mov DWORD PTR [esp+3336], ecx
	mov DWORD PTR [esp+3340], ecx
	mov DWORD PTR [esp+3344], ecx
	mov DWORD PTR [esp+3348], ecx
	mov DWORD PTR [esp+3352], ecx
	mov DWORD PTR [esp+3356], ecx
	mov DWORD PTR [esp+3360], ecx
	mov DWORD PTR [esp+3364], ecx
	mov DWORD PTR [esp+3368], ecx
	mov DWORD PTR [esp+3372], ecx
	mov DWORD PTR [esp+3376], ecx
	mov DWORD PTR [esp+3380], ecx
	mov DWORD PTR [esp+3384], ecx
	mov DWORD PTR [esp+3388], ecx
	mov DWORD PTR [esp+3392], ecx
	mov DWORD PTR [esp+3396], ecx
	mov DWORD PTR [esp+3400], ecx
	mov DWORD PTR [esp+3404], ecx
	mov DWORD PTR [esp+3408], ecx
	mov DWORD PTR [esp+3412], ecx
	mov DWORD PTR [esp+3416], ecx
	mov DWORD PTR [esp+3420], ecx
	mov DWORD PTR [esp+3424], ecx
	mov DWORD PTR [esp+3428], ecx
	lea esp, [esp+3432]
	jmp 21b
	.p2align 6

vg_hmac_sha512_224_finalize:
	lea esp, [esp-1900]
	mov eax, DWORD PTR [esp+1904]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1908]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1912]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1916]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1920]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+272], ebx
	mov DWORD PTR [eax+276], esi
	mov DWORD PTR [eax+280], edi
	mov DWORD PTR [eax+284], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, ebp
	add edx, 288
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, DWORD PTR [esi]
	mov DWORD PTR [ebx], ecx
	mov ecx, DWORD PTR [esi+4]
	mov DWORD PTR [ebx+4], ecx
	mov ecx, DWORD PTR [esi+8]
	mov DWORD PTR [ebx+8], ecx
	mov ecx, DWORD PTR [esi+12]
	mov DWORD PTR [ebx+12], ecx
	mov ecx, DWORD PTR [esi+16]
	mov DWORD PTR [ebx+16], ecx
	mov ecx, DWORD PTR [esi+20]
	mov DWORD PTR [ebx+20], ecx
	mov ecx, DWORD PTR [esi+24]
	mov DWORD PTR [ebx+24], ecx
	mov ecx, DWORD PTR [esi+28]
	mov DWORD PTR [ebx+28], ecx
	mov ecx, DWORD PTR [esi+32]
	mov DWORD PTR [ebx+32], ecx
	mov ecx, DWORD PTR [esi+36]
	mov DWORD PTR [ebx+36], ecx
	mov ecx, DWORD PTR [esi+40]
	mov DWORD PTR [ebx+40], ecx
	mov ecx, DWORD PTR [esi+44]
	mov DWORD PTR [ebx+44], ecx
	mov ecx, DWORD PTR [esi+48]
	mov DWORD PTR [ebx+48], ecx
	mov ecx, DWORD PTR [esi+52]
	mov DWORD PTR [ebx+52], ecx
	mov ecx, DWORD PTR [esi+56]
	mov DWORD PTR [ebx+56], ecx
	mov ecx, DWORD PTR [esi+60]
	mov DWORD PTR [ebx+60], ecx
	mov ecx, DWORD PTR [ebp+288]
	mov DWORD PTR [ebx+64], ecx
	mov ecx, DWORD PTR [ebp+292]
	mov DWORD PTR [ebx+68], ecx
	mov ecx, DWORD PTR [ebp+296]
	mov DWORD PTR [ebx+72], ecx
	mov ecx, DWORD PTR [ebp+300]
	mov DWORD PTR [ebx+76], ecx
	mov ecx, DWORD PTR [ebp+304]
	mov DWORD PTR [ebx+80], ecx
	mov ecx, DWORD PTR [ebp+308]
	mov DWORD PTR [ebx+84], ecx
	mov ecx, DWORD PTR [ebp+312]
	mov DWORD PTR [ebx+88], ecx
	mov ecx, 128
	mov DWORD PTR [ebx+92], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+96], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+100], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+104], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+108], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+112], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+116], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+120], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+124], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+128], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+132], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+136], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+140], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+144], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+148], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+152], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+156], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+160], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+164], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+168], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+172], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+176], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+180], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+184], ecx
	mov ecx, -536608768
	mov DWORD PTR [ebx+188], ecx
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebx
	add eax, 64
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov ecx, DWORD PTR [ebx+36]
	bswap ecx
	mov DWORD PTR [eax+32], ecx
	mov ecx, DWORD PTR [ebx+32]
	bswap ecx
	mov DWORD PTR [eax+36], ecx
	mov ecx, DWORD PTR [ebx+44]
	bswap ecx
	mov DWORD PTR [eax+40], ecx
	mov ecx, DWORD PTR [ebx+40]
	bswap ecx
	mov DWORD PTR [eax+44], ecx
	mov ecx, DWORD PTR [ebx+52]
	bswap ecx
	mov DWORD PTR [eax+48], ecx
	mov ecx, DWORD PTR [ebx+48]
	bswap ecx
	mov DWORD PTR [eax+52], ecx
	mov ecx, DWORD PTR [ebx+60]
	bswap ecx
	mov DWORD PTR [eax+56], ecx
	mov ecx, DWORD PTR [ebx+56]
	bswap ecx
	mov DWORD PTR [eax+60], ecx
	mov ecx, DWORD PTR [ebx+64]
	mov DWORD PTR [edi], ecx
	mov ecx, DWORD PTR [ebx+68]
	mov DWORD PTR [edi+4], ecx
	mov ecx, DWORD PTR [ebx+72]
	mov DWORD PTR [edi+8], ecx
	mov ecx, DWORD PTR [ebx+76]
	mov DWORD PTR [edi+12], ecx
	mov ecx, DWORD PTR [ebx+80]
	mov DWORD PTR [edi+16], ecx
	mov ecx, DWORD PTR [ebx+84]
	mov DWORD PTR [edi+20], ecx
	mov ecx, DWORD PTR [ebx+88]
	mov DWORD PTR [edi+24], ecx
	mov eax, ebp
	mov ebx, DWORD PTR [eax+272]
	mov esi, DWORD PTR [eax+276]
	mov edi, DWORD PTR [eax+280]
	mov ebp, DWORD PTR [eax+284]
	lea esp, [esp+1900]
	ret
	.p2align 6

vg_hmac_sha512_224_init_scratch:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+272], ebx
	mov DWORD PTR [eax+276], esi
	mov DWORD PTR [eax+280], edi
	mov DWORD PTR [eax+284], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	push ebx
	call {vg_sha512_224_init}
	pop eax
	push esi
	call {vg_sha512_224_init}
	pop eax
	mov ecx, 909522486
	mov DWORD PTR [ebx+64], ecx
	mov DWORD PTR [ebx+68], ecx
	mov DWORD PTR [ebx+72], ecx
	mov DWORD PTR [ebx+76], ecx
	mov DWORD PTR [ebx+80], ecx
	mov DWORD PTR [ebx+84], ecx
	mov DWORD PTR [ebx+88], ecx
	mov DWORD PTR [ebx+92], ecx
	mov DWORD PTR [ebx+96], ecx
	mov DWORD PTR [ebx+100], ecx
	mov DWORD PTR [ebx+104], ecx
	mov DWORD PTR [ebx+108], ecx
	mov DWORD PTR [ebx+112], ecx
	mov DWORD PTR [ebx+116], ecx
	mov DWORD PTR [ebx+120], ecx
	mov DWORD PTR [ebx+124], ecx
	mov DWORD PTR [ebx+128], ecx
	mov DWORD PTR [ebx+132], ecx
	mov DWORD PTR [ebx+136], ecx
	mov DWORD PTR [ebx+140], ecx
	mov DWORD PTR [ebx+144], ecx
	mov DWORD PTR [ebx+148], ecx
	mov DWORD PTR [ebx+152], ecx
	mov DWORD PTR [ebx+156], ecx
	mov DWORD PTR [ebx+160], ecx
	mov DWORD PTR [ebx+164], ecx
	mov DWORD PTR [ebx+168], ecx
	mov DWORD PTR [ebx+172], ecx
	mov DWORD PTR [ebx+176], ecx
	mov DWORD PTR [ebx+180], ecx
	mov DWORD PTR [ebx+184], ecx
	mov DWORD PTR [ebx+188], ecx
	mov edi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, ebx
	add edx, 64
	test ecx, ecx
	je 20f
22:
	movzx eax, BYTE PTR [edi]
	xor eax, 54
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebx+64]
	xor eax, 1785358954
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [ebx+68]
	xor eax, 1785358954
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [ebx+72]
	xor eax, 1785358954
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [ebx+76]
	xor eax, 1785358954
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [ebx+80]
	xor eax, 1785358954
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [ebx+84]
	xor eax, 1785358954
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [ebx+88]
	xor eax, 1785358954
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [ebx+92]
	xor eax, 1785358954
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [ebx+96]
	xor eax, 1785358954
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [ebx+100]
	xor eax, 1785358954
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [ebx+104]
	xor eax, 1785358954
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [ebx+108]
	xor eax, 1785358954
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [ebx+112]
	xor eax, 1785358954
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [ebx+116]
	xor eax, 1785358954
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [ebx+120]
	xor eax, 1785358954
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [ebx+124]
	xor eax, 1785358954
	mov DWORD PTR [esi+124], eax
	mov eax, DWORD PTR [ebx+128]
	xor eax, 1785358954
	mov DWORD PTR [esi+128], eax
	mov eax, DWORD PTR [ebx+132]
	xor eax, 1785358954
	mov DWORD PTR [esi+132], eax
	mov eax, DWORD PTR [ebx+136]
	xor eax, 1785358954
	mov DWORD PTR [esi+136], eax
	mov eax, DWORD PTR [ebx+140]
	xor eax, 1785358954
	mov DWORD PTR [esi+140], eax
	mov eax, DWORD PTR [ebx+144]
	xor eax, 1785358954
	mov DWORD PTR [esi+144], eax
	mov eax, DWORD PTR [ebx+148]
	xor eax, 1785358954
	mov DWORD PTR [esi+148], eax
	mov eax, DWORD PTR [ebx+152]
	xor eax, 1785358954
	mov DWORD PTR [esi+152], eax
	mov eax, DWORD PTR [ebx+156]
	xor eax, 1785358954
	mov DWORD PTR [esi+156], eax
	mov eax, DWORD PTR [ebx+160]
	xor eax, 1785358954
	mov DWORD PTR [esi+160], eax
	mov eax, DWORD PTR [ebx+164]
	xor eax, 1785358954
	mov DWORD PTR [esi+164], eax
	mov eax, DWORD PTR [ebx+168]
	xor eax, 1785358954
	mov DWORD PTR [esi+168], eax
	mov eax, DWORD PTR [ebx+172]
	xor eax, 1785358954
	mov DWORD PTR [esi+172], eax
	mov eax, DWORD PTR [ebx+176]
	xor eax, 1785358954
	mov DWORD PTR [esi+176], eax
	mov eax, DWORD PTR [ebx+180]
	xor eax, 1785358954
	mov DWORD PTR [esi+180], eax
	mov eax, DWORD PTR [ebx+184]
	xor eax, 1785358954
	mov DWORD PTR [esi+184], eax
	mov eax, DWORD PTR [ebx+188]
	xor eax, 1785358954
	mov DWORD PTR [esi+188], eax
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, esi
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	mov ebx, DWORD PTR [eax+272]
	mov esi, DWORD PTR [eax+276]
	mov edi, DWORD PTR [eax+280]
	mov ebp, DWORD PTR [eax+284]
	ret
	.p2align 6

vg_hmac_sha512_224_finalize_scratch:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+272], ebx
	mov DWORD PTR [eax+276], esi
	mov DWORD PTR [eax+280], edi
	mov DWORD PTR [eax+284], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, ebp
	add edx, 288
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, DWORD PTR [esi]
	mov DWORD PTR [ebx], ecx
	mov ecx, DWORD PTR [esi+4]
	mov DWORD PTR [ebx+4], ecx
	mov ecx, DWORD PTR [esi+8]
	mov DWORD PTR [ebx+8], ecx
	mov ecx, DWORD PTR [esi+12]
	mov DWORD PTR [ebx+12], ecx
	mov ecx, DWORD PTR [esi+16]
	mov DWORD PTR [ebx+16], ecx
	mov ecx, DWORD PTR [esi+20]
	mov DWORD PTR [ebx+20], ecx
	mov ecx, DWORD PTR [esi+24]
	mov DWORD PTR [ebx+24], ecx
	mov ecx, DWORD PTR [esi+28]
	mov DWORD PTR [ebx+28], ecx
	mov ecx, DWORD PTR [esi+32]
	mov DWORD PTR [ebx+32], ecx
	mov ecx, DWORD PTR [esi+36]
	mov DWORD PTR [ebx+36], ecx
	mov ecx, DWORD PTR [esi+40]
	mov DWORD PTR [ebx+40], ecx
	mov ecx, DWORD PTR [esi+44]
	mov DWORD PTR [ebx+44], ecx
	mov ecx, DWORD PTR [esi+48]
	mov DWORD PTR [ebx+48], ecx
	mov ecx, DWORD PTR [esi+52]
	mov DWORD PTR [ebx+52], ecx
	mov ecx, DWORD PTR [esi+56]
	mov DWORD PTR [ebx+56], ecx
	mov ecx, DWORD PTR [esi+60]
	mov DWORD PTR [ebx+60], ecx
	mov ecx, DWORD PTR [ebp+288]
	mov DWORD PTR [ebx+64], ecx
	mov ecx, DWORD PTR [ebp+292]
	mov DWORD PTR [ebx+68], ecx
	mov ecx, DWORD PTR [ebp+296]
	mov DWORD PTR [ebx+72], ecx
	mov ecx, DWORD PTR [ebp+300]
	mov DWORD PTR [ebx+76], ecx
	mov ecx, DWORD PTR [ebp+304]
	mov DWORD PTR [ebx+80], ecx
	mov ecx, DWORD PTR [ebp+308]
	mov DWORD PTR [ebx+84], ecx
	mov ecx, DWORD PTR [ebp+312]
	mov DWORD PTR [ebx+88], ecx
	mov ecx, 128
	mov DWORD PTR [ebx+92], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+96], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+100], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+104], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+108], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+112], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+116], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+120], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+124], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+128], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+132], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+136], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+140], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+144], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+148], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+152], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+156], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+160], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+164], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+168], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+172], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+176], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+180], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+184], ecx
	mov ecx, -536608768
	mov DWORD PTR [ebx+188], ecx
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebx
	add eax, 64
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov ecx, DWORD PTR [ebx+36]
	bswap ecx
	mov DWORD PTR [eax+32], ecx
	mov ecx, DWORD PTR [ebx+32]
	bswap ecx
	mov DWORD PTR [eax+36], ecx
	mov ecx, DWORD PTR [ebx+44]
	bswap ecx
	mov DWORD PTR [eax+40], ecx
	mov ecx, DWORD PTR [ebx+40]
	bswap ecx
	mov DWORD PTR [eax+44], ecx
	mov ecx, DWORD PTR [ebx+52]
	bswap ecx
	mov DWORD PTR [eax+48], ecx
	mov ecx, DWORD PTR [ebx+48]
	bswap ecx
	mov DWORD PTR [eax+52], ecx
	mov ecx, DWORD PTR [ebx+60]
	bswap ecx
	mov DWORD PTR [eax+56], ecx
	mov ecx, DWORD PTR [ebx+56]
	bswap ecx
	mov DWORD PTR [eax+60], ecx
	mov ecx, DWORD PTR [ebx+64]
	mov DWORD PTR [edi], ecx
	mov ecx, DWORD PTR [ebx+68]
	mov DWORD PTR [edi+4], ecx
	mov ecx, DWORD PTR [ebx+72]
	mov DWORD PTR [edi+8], ecx
	mov ecx, DWORD PTR [ebx+76]
	mov DWORD PTR [edi+12], ecx
	mov ecx, DWORD PTR [ebx+80]
	mov DWORD PTR [edi+16], ecx
	mov ecx, DWORD PTR [ebx+84]
	mov DWORD PTR [edi+20], ecx
	mov ecx, DWORD PTR [ebx+88]
	mov DWORD PTR [edi+24], ecx
	mov eax, ebp
	mov ebx, DWORD PTR [eax+272]
	mov esi, DWORD PTR [eax+276]
	mov edi, DWORD PTR [eax+280]
	mov ebp, DWORD PTR [eax+284]
	ret
	.p2align 6
