// The functions of `src/hmac_md5.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_md5_init:
	mov eax, DWORD PTR [esp+16]
	cmp eax, 65
	jae 20f
	lea esp, [esp-408]
	mov eax, DWORD PTR [esp+412]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+416]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+420]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+424]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+112], ebx
	mov DWORD PTR [eax+116], esi
	mov DWORD PTR [eax+120], edi
	mov DWORD PTR [eax+124], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	push ebx
	call {vg_md5_init}
	pop eax
	push esi
	call {vg_md5_init}
	pop eax
	mov ecx, 909522486
	mov DWORD PTR [ebx+16], ecx
	mov DWORD PTR [ebx+20], ecx
	mov DWORD PTR [ebx+24], ecx
	mov DWORD PTR [ebx+28], ecx
	mov DWORD PTR [ebx+32], ecx
	mov DWORD PTR [ebx+36], ecx
	mov DWORD PTR [ebx+40], ecx
	mov DWORD PTR [ebx+44], ecx
	mov DWORD PTR [ebx+48], ecx
	mov DWORD PTR [ebx+52], ecx
	mov DWORD PTR [ebx+56], ecx
	mov DWORD PTR [ebx+60], ecx
	mov DWORD PTR [ebx+64], ecx
	mov DWORD PTR [ebx+68], ecx
	mov DWORD PTR [ebx+72], ecx
	mov DWORD PTR [ebx+76], ecx
	mov edi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, ebx
	add edx, 16
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
	mov eax, DWORD PTR [ebx+16]
	xor eax, 1785358954
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [ebx+20]
	xor eax, 1785358954
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [ebx+24]
	xor eax, 1785358954
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [ebx+28]
	xor eax, 1785358954
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [ebx+32]
	xor eax, 1785358954
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [ebx+36]
	xor eax, 1785358954
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [ebx+40]
	xor eax, 1785358954
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [ebx+44]
	xor eax, 1785358954
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [ebx+48]
	xor eax, 1785358954
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [ebx+52]
	xor eax, 1785358954
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [ebx+56]
	xor eax, 1785358954
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [ebx+60]
	xor eax, 1785358954
	mov DWORD PTR [esi+60], eax
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
	mov eax, ebx
	add eax, 16
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_md5_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, esi
	mov eax, ebx
	add eax, 16
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_md5_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	mov ebx, DWORD PTR [eax+112]
	mov esi, DWORD PTR [eax+116]
	mov edi, DWORD PTR [eax+120]
	mov ebp, DWORD PTR [eax+124]
	lea esp, [esp+408]
21:
	ret
20:
	lea esp, [esp-1048]
	mov eax, DWORD PTR [esp+1052]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1056]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1060]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1064]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+384], ebx
	mov DWORD PTR [eax+388], esi
	mov DWORD PTR [eax+392], edi
	mov DWORD PTR [eax+396], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+16]
	cmp ecx, 65
	jae 25f
	mov edx, DWORD PTR [esp+12]
	jmp 26f
25:
	mov edi, ebp
	add edi, 640
	push edi
	call {vg_md5_init}
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
	call {vg_md5_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+16]
	mov ecx, 0
	mov edx, ebp
	add edx, 752
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_md5_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 752
	mov ecx, 16
26:
	mov edi, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_md5_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	mov ebx, DWORD PTR [eax+384]
	mov esi, DWORD PTR [eax+388]
	mov edi, DWORD PTR [eax+392]
	mov ebp, DWORD PTR [eax+396]
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
	lea esp, [esp+1048]
	jmp 21b
	.p2align 6

vg_hmac_md5_finalize:
	lea esp, [esp-412]
	mov eax, DWORD PTR [esp+416]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+420]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+424]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+428]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+432]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+112], ebx
	mov DWORD PTR [eax+116], esi
	mov DWORD PTR [eax+120], edi
	mov DWORD PTR [eax+124], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, ebp
	add edx, 128
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_md5_finalize_scratch}
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
	mov ecx, DWORD PTR [ebp+128]
	mov DWORD PTR [ebx+16], ecx
	mov ecx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebx+20], ecx
	mov ecx, DWORD PTR [ebp+136]
	mov DWORD PTR [ebx+24], ecx
	mov ecx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebx+28], ecx
	mov ecx, 128
	mov DWORD PTR [ebx+32], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+36], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+40], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+44], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+48], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+52], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+56], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+60], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+64], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+68], ecx
	mov ecx, 640
	mov DWORD PTR [ebx+72], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+76], ecx
	mov eax, ebx
	add eax, 16
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_md5_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	mov ecx, DWORD PTR [ebx]
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	mov DWORD PTR [eax+12], ecx
	mov eax, ebp
	mov ebx, DWORD PTR [eax+112]
	mov esi, DWORD PTR [eax+116]
	mov edi, DWORD PTR [eax+120]
	mov ebp, DWORD PTR [eax+124]
	lea esp, [esp+412]
	ret
	.p2align 6

vg_hmac_md5_init_scratch:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+112], ebx
	mov DWORD PTR [eax+116], esi
	mov DWORD PTR [eax+120], edi
	mov DWORD PTR [eax+124], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	push ebx
	call {vg_md5_init}
	pop eax
	push esi
	call {vg_md5_init}
	pop eax
	mov ecx, 909522486
	mov DWORD PTR [ebx+16], ecx
	mov DWORD PTR [ebx+20], ecx
	mov DWORD PTR [ebx+24], ecx
	mov DWORD PTR [ebx+28], ecx
	mov DWORD PTR [ebx+32], ecx
	mov DWORD PTR [ebx+36], ecx
	mov DWORD PTR [ebx+40], ecx
	mov DWORD PTR [ebx+44], ecx
	mov DWORD PTR [ebx+48], ecx
	mov DWORD PTR [ebx+52], ecx
	mov DWORD PTR [ebx+56], ecx
	mov DWORD PTR [ebx+60], ecx
	mov DWORD PTR [ebx+64], ecx
	mov DWORD PTR [ebx+68], ecx
	mov DWORD PTR [ebx+72], ecx
	mov DWORD PTR [ebx+76], ecx
	mov edi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, ebx
	add edx, 16
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
	mov eax, DWORD PTR [ebx+16]
	xor eax, 1785358954
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [ebx+20]
	xor eax, 1785358954
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [ebx+24]
	xor eax, 1785358954
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [ebx+28]
	xor eax, 1785358954
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [ebx+32]
	xor eax, 1785358954
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [ebx+36]
	xor eax, 1785358954
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [ebx+40]
	xor eax, 1785358954
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [ebx+44]
	xor eax, 1785358954
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [ebx+48]
	xor eax, 1785358954
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [ebx+52]
	xor eax, 1785358954
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [ebx+56]
	xor eax, 1785358954
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [ebx+60]
	xor eax, 1785358954
	mov DWORD PTR [esi+60], eax
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
	mov eax, ebx
	add eax, 16
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_md5_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, esi
	mov eax, ebx
	add eax, 16
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_md5_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	mov ebx, DWORD PTR [eax+112]
	mov esi, DWORD PTR [eax+116]
	mov edi, DWORD PTR [eax+120]
	mov ebp, DWORD PTR [eax+124]
	ret
	.p2align 6

vg_hmac_md5_finalize_scratch:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+112], ebx
	mov DWORD PTR [eax+116], esi
	mov DWORD PTR [eax+120], edi
	mov DWORD PTR [eax+124], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, ebp
	add edx, 128
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_md5_finalize_scratch}
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
	mov ecx, DWORD PTR [ebp+128]
	mov DWORD PTR [ebx+16], ecx
	mov ecx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebx+20], ecx
	mov ecx, DWORD PTR [ebp+136]
	mov DWORD PTR [ebx+24], ecx
	mov ecx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebx+28], ecx
	mov ecx, 128
	mov DWORD PTR [ebx+32], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+36], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+40], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+44], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+48], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+52], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+56], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+60], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+64], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+68], ecx
	mov ecx, 640
	mov DWORD PTR [ebx+72], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+76], ecx
	mov eax, ebx
	add eax, 16
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_md5_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	mov ecx, DWORD PTR [ebx]
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	mov DWORD PTR [eax+12], ecx
	mov eax, ebp
	mov ebx, DWORD PTR [eax+112]
	mov esi, DWORD PTR [eax+116]
	mov edi, DWORD PTR [eax+120]
	mov ebp, DWORD PTR [eax+124]
	ret
	.p2align 6
