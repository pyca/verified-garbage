// The functions of `src/ec_p192_compressed.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p192_compress_public_key:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+828], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+852], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+876], eax
	mov eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, -1
	mov DWORD PTR [edi+68], eax
	mov eax, -2
	mov DWORD PTR [edi+72], eax
	mov eax, -1
	mov DWORD PTR [edi+76], eax
	mov eax, -1
	mov DWORD PTR [edi+80], eax
	mov eax, -1
	mov DWORD PTR [edi+84], eax
	mov eax, -1261295567
	mov DWORD PTR [edi+88], eax
	mov eax, 342608305
	mov DWORD PTR [edi+92], eax
	mov eax, -1713440714
	mov DWORD PTR [edi+96], eax
	mov eax, -1
	mov DWORD PTR [edi+100], eax
	mov eax, -1
	mov DWORD PTR [edi+104], eax
	mov eax, -1
	mov DWORD PTR [edi+108], eax
	mov eax, 0
	mov DWORD PTR [edi+136], eax
	mov eax, 0
	mov DWORD PTR [edi+140], eax
	mov eax, 0
	mov DWORD PTR [edi+144], eax
	mov eax, 0
	mov DWORD PTR [edi+148], eax
	mov eax, 0
	mov DWORD PTR [edi+152], eax
	mov eax, 0
	mov DWORD PTR [edi+156], eax
	mov eax, 1
	mov DWORD PTR [edi+160], eax
	mov eax, 0
	mov DWORD PTR [edi+164], eax
	mov eax, 0
	mov DWORD PTR [edi+168], eax
	mov eax, 0
	mov DWORD PTR [edi+172], eax
	mov eax, 0
	mov DWORD PTR [edi+176], eax
	mov eax, 0
	mov DWORD PTR [edi+180], eax
	mov eax, 1
	mov DWORD PTR [edi+184], eax
	mov eax, 0
	mov DWORD PTR [edi+188], eax
	mov eax, 1
	mov DWORD PTR [edi+192], eax
	mov eax, 0
	mov DWORD PTR [edi+196], eax
	mov eax, 0
	mov DWORD PTR [edi+200], eax
	mov eax, 0
	mov DWORD PTR [edi+204], eax
	mov eax, -4
	mov DWORD PTR [edi+208], eax
	mov eax, -1
	mov DWORD PTR [edi+212], eax
	mov eax, -5
	mov DWORD PTR [edi+216], eax
	mov eax, -1
	mov DWORD PTR [edi+220], eax
	mov eax, -1
	mov DWORD PTR [edi+224], eax
	mov eax, -1
	mov DWORD PTR [edi+228], eax
	mov eax, -190206007
	mov DWORD PTR [edi+232], eax
	mov eax, 680373267
	mov DWORD PTR [edi+236], eax
	mov eax, 1259749544
	mov DWORD PTR [edi+240], eax
	mov eax, 1468360982
	mov DWORD PTR [edi+244], eax
	mov eax, 121770900
	mov DWORD PTR [edi+248], eax
	mov eax, 1532677200
	mov DWORD PTR [edi+252], eax
	mov eax, 858759432
	mov DWORD PTR [edi+256], eax
	mov eax, 227324684
	mov DWORD PTR [edi+260], eax
	mov eax, 1993419017
	mov DWORD PTR [edi+264], eax
	mov eax, -1974742025
	mov DWORD PTR [edi+268], eax
	mov eax, -204334857
	mov DWORD PTR [edi+272], eax
	mov eax, -1790129927
	mov DWORD PTR [edi+276], eax
	mov eax, 507650697
	mov DWORD PTR [edi+280], eax
	mov eax, 2064818999
	mov DWORD PTR [edi+284], eax
	mov eax, -1989742498
	mov DWORD PTR [edi+288], eax
	mov eax, -568150748
	mov DWORD PTR [edi+292], eax
	mov eax, 1793960013
	mov DWORD PTR [edi+296], eax
	mov eax, 1781087619
	mov DWORD PTR [edi+300], eax
	mov eax, -558671519
	mov DWORD PTR [edi+304], eax
	mov eax, -832128308
	mov DWORD PTR [edi+308], eax
	mov eax, -1153799186
	mov DWORD PTR [edi+312], eax
	mov eax, 1184295515
	mov DWORD PTR [edi+316], eax
	mov eax, -368737886
	mov DWORD PTR [edi+320], eax
	mov eax, 683562615
	mov DWORD PTR [edi+324], eax
	mov eax, 1261295567
	mov DWORD PTR [edi+328], eax
	mov eax, -342608306
	mov DWORD PTR [edi+332], eax
	mov eax, 1713440713
	mov DWORD PTR [edi+336], eax
	mov eax, 0
	mov DWORD PTR [edi+340], eax
	mov eax, 0
	mov DWORD PTR [edi+344], eax
	mov eax, 0
	mov DWORD PTR [edi+348], eax
	mov eax, -3
	mov DWORD PTR [edi+352], eax
	mov eax, -1
	mov DWORD PTR [edi+356], eax
	mov eax, -2
	mov DWORD PTR [edi+360], eax
	mov eax, -1
	mov DWORD PTR [edi+364], eax
	mov eax, -1
	mov DWORD PTR [edi+368], eax
	mov eax, -1
	mov DWORD PTR [edi+372], eax
	mov eax, -1261295569
	mov DWORD PTR [edi+376], eax
	mov eax, 342608305
	mov DWORD PTR [edi+380], eax
	mov eax, -1713440714
	mov DWORD PTR [edi+384], eax
	mov eax, -1
	mov DWORD PTR [edi+388], eax
	mov eax, -1
	mov DWORD PTR [edi+392], eax
	mov eax, -1
	mov DWORD PTR [edi+396], eax
	mov eax, 0
	mov DWORD PTR [edi+400], eax
	mov eax, 0
	mov DWORD PTR [edi+404], eax
	mov eax, 0
	mov DWORD PTR [edi+408], eax
	mov eax, 0
	mov DWORD PTR [edi+412], eax
	mov eax, 0
	mov DWORD PTR [edi+416], eax
	mov eax, 0
	mov DWORD PTR [edi+420], eax
	mov eax, 1
	mov DWORD PTR [edi+424], eax
	mov eax, 0
	mov DWORD PTR [edi+428], eax
	mov eax, 1
	mov DWORD PTR [edi+432], eax
	mov eax, 0
	mov DWORD PTR [edi+436], eax
	mov eax, 0
	mov DWORD PTR [edi+440], eax
	mov eax, 0
	mov DWORD PTR [edi+444], eax
	mov eax, 0
	mov DWORD PTR [edi+448], eax
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov eax, 0
	mov DWORD PTR [edi+456], eax
	mov eax, 0
	mov DWORD PTR [edi+460], eax
	mov eax, 0
	mov DWORD PTR [edi+464], eax
	mov eax, 0
	mov DWORD PTR [edi+468], eax
	mov eax, -1
	mov DWORD PTR [edi+1120], eax
	mov eax, 1
	mov DWORD PTR [edi+1000], eax
	mov eax, 0
	mov DWORD PTR [edi+1004], eax
	mov eax, 2
	mov DWORD PTR [edi+1008], eax
	mov eax, 0
	mov DWORD PTR [edi+1012], eax
	mov eax, 1
	mov DWORD PTR [edi+1016], eax
	mov eax, 0
	mov DWORD PTR [edi+1020], eax
	mov eax, -1495057768
	mov DWORD PTR [edi+1024], eax
	mov eax, 1658446854
	mov DWORD PTR [edi+1028], eax
	mov eax, 419916514
	mov DWORD PTR [edi+1032], eax
	mov eax, 1921109426
	mov DWORD PTR [edi+1036], eax
	mov eax, 1472246065
	mov DWORD PTR [edi+1040], eax
	mov eax, 1942548165
	mov DWORD PTR [edi+1044], eax
	mov ebx, DWORD PTR [esp+8]
	add ebx, 1
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+876], eax
	add ebx, 24
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+936], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+940], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+944], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+948], eax
	mov ebx, DWORD PTR [esp+8]
	movzx edx, BYTE PTR [ebx]
	xor edx, 4
	sub edx, 1
	sbb edx, edx
	mov eax, DWORD PTR [edi+1120]
	and eax, edx
	mov DWORD PTR [edi+1120], eax
	mov edx, DWORD PTR [edi+856]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+860]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+864]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+868]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+872]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+876]
	sbb edx, DWORD PTR [edi+84]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+1120]
	and eax, edx
	mov DWORD PTR [edi+1120], eax
	mov edx, DWORD PTR [edi+928]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+932]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+936]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+940]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+944]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+948]
	sbb edx, DWORD PTR [edi+84]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+1120]
	and eax, edx
	mov DWORD PTR [edi+1120], eax
	mov eax, 1000
	mov ecx, 856
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1000
	mov ecx, 928
	mov edx, 904
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 904
	mov ecx, 904
	mov edx, 952
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 880
	mov ecx, 880
	mov edx, 1048
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 880
	mov ecx, 1048
	mov edx, 1072
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 880
	mov ecx, 208
	mov edx, 1048
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1048
	mov ecx, 1072
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 976
	mov edx, 1072
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1072
	mov ecx, 952
	mov edx, 1048
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1048]
	or edx, DWORD PTR [edi+1052]
	or edx, DWORD PTR [edi+1056]
	or edx, DWORD PTR [edi+1060]
	or edx, DWORD PTR [edi+1064]
	or edx, DWORD PTR [edi+1068]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+1120]
	and eax, edx
	mov DWORD PTR [edi+1120], eax
	mov ecx, DWORD PTR [edi+1120]
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+896]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+900]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+904]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+908]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+912]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+916]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+920]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+924]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1116], eax
	mov ecx, DWORD PTR [edi+1120]
	mov ebx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+928]
	and eax, 1
	or eax, 2
	and eax, ecx
	mov BYTE PTR [ebx], al
	mov eax, DWORD PTR [edi+856]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+21], eax
	mov eax, DWORD PTR [edi+860]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+17], eax
	mov eax, DWORD PTR [edi+864]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+13], eax
	mov eax, DWORD PTR [edi+868]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+9], eax
	mov eax, DWORD PTR [edi+872]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+5], eax
	mov eax, DWORD PTR [edi+876]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+1], eax
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	ret
	.p2align 6

vg_ec_p192_decompress_public_key:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+828], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+852], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+876], eax
	mov eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, -1
	mov DWORD PTR [edi+68], eax
	mov eax, -2
	mov DWORD PTR [edi+72], eax
	mov eax, -1
	mov DWORD PTR [edi+76], eax
	mov eax, -1
	mov DWORD PTR [edi+80], eax
	mov eax, -1
	mov DWORD PTR [edi+84], eax
	mov eax, -1261295567
	mov DWORD PTR [edi+88], eax
	mov eax, 342608305
	mov DWORD PTR [edi+92], eax
	mov eax, -1713440714
	mov DWORD PTR [edi+96], eax
	mov eax, -1
	mov DWORD PTR [edi+100], eax
	mov eax, -1
	mov DWORD PTR [edi+104], eax
	mov eax, -1
	mov DWORD PTR [edi+108], eax
	mov eax, 0
	mov DWORD PTR [edi+136], eax
	mov eax, 0
	mov DWORD PTR [edi+140], eax
	mov eax, 0
	mov DWORD PTR [edi+144], eax
	mov eax, 0
	mov DWORD PTR [edi+148], eax
	mov eax, 0
	mov DWORD PTR [edi+152], eax
	mov eax, 0
	mov DWORD PTR [edi+156], eax
	mov eax, 1
	mov DWORD PTR [edi+160], eax
	mov eax, 0
	mov DWORD PTR [edi+164], eax
	mov eax, 0
	mov DWORD PTR [edi+168], eax
	mov eax, 0
	mov DWORD PTR [edi+172], eax
	mov eax, 0
	mov DWORD PTR [edi+176], eax
	mov eax, 0
	mov DWORD PTR [edi+180], eax
	mov eax, 1
	mov DWORD PTR [edi+184], eax
	mov eax, 0
	mov DWORD PTR [edi+188], eax
	mov eax, 1
	mov DWORD PTR [edi+192], eax
	mov eax, 0
	mov DWORD PTR [edi+196], eax
	mov eax, 0
	mov DWORD PTR [edi+200], eax
	mov eax, 0
	mov DWORD PTR [edi+204], eax
	mov eax, -4
	mov DWORD PTR [edi+208], eax
	mov eax, -1
	mov DWORD PTR [edi+212], eax
	mov eax, -5
	mov DWORD PTR [edi+216], eax
	mov eax, -1
	mov DWORD PTR [edi+220], eax
	mov eax, -1
	mov DWORD PTR [edi+224], eax
	mov eax, -1
	mov DWORD PTR [edi+228], eax
	mov eax, -190206007
	mov DWORD PTR [edi+232], eax
	mov eax, 680373267
	mov DWORD PTR [edi+236], eax
	mov eax, 1259749544
	mov DWORD PTR [edi+240], eax
	mov eax, 1468360982
	mov DWORD PTR [edi+244], eax
	mov eax, 121770900
	mov DWORD PTR [edi+248], eax
	mov eax, 1532677200
	mov DWORD PTR [edi+252], eax
	mov eax, 858759432
	mov DWORD PTR [edi+256], eax
	mov eax, 227324684
	mov DWORD PTR [edi+260], eax
	mov eax, 1993419017
	mov DWORD PTR [edi+264], eax
	mov eax, -1974742025
	mov DWORD PTR [edi+268], eax
	mov eax, -204334857
	mov DWORD PTR [edi+272], eax
	mov eax, -1790129927
	mov DWORD PTR [edi+276], eax
	mov eax, 507650697
	mov DWORD PTR [edi+280], eax
	mov eax, 2064818999
	mov DWORD PTR [edi+284], eax
	mov eax, -1989742498
	mov DWORD PTR [edi+288], eax
	mov eax, -568150748
	mov DWORD PTR [edi+292], eax
	mov eax, 1793960013
	mov DWORD PTR [edi+296], eax
	mov eax, 1781087619
	mov DWORD PTR [edi+300], eax
	mov eax, -558671519
	mov DWORD PTR [edi+304], eax
	mov eax, -832128308
	mov DWORD PTR [edi+308], eax
	mov eax, -1153799186
	mov DWORD PTR [edi+312], eax
	mov eax, 1184295515
	mov DWORD PTR [edi+316], eax
	mov eax, -368737886
	mov DWORD PTR [edi+320], eax
	mov eax, 683562615
	mov DWORD PTR [edi+324], eax
	mov eax, 1261295567
	mov DWORD PTR [edi+328], eax
	mov eax, -342608306
	mov DWORD PTR [edi+332], eax
	mov eax, 1713440713
	mov DWORD PTR [edi+336], eax
	mov eax, 0
	mov DWORD PTR [edi+340], eax
	mov eax, 0
	mov DWORD PTR [edi+344], eax
	mov eax, 0
	mov DWORD PTR [edi+348], eax
	mov eax, -3
	mov DWORD PTR [edi+352], eax
	mov eax, -1
	mov DWORD PTR [edi+356], eax
	mov eax, -2
	mov DWORD PTR [edi+360], eax
	mov eax, -1
	mov DWORD PTR [edi+364], eax
	mov eax, -1
	mov DWORD PTR [edi+368], eax
	mov eax, -1
	mov DWORD PTR [edi+372], eax
	mov eax, -1261295569
	mov DWORD PTR [edi+376], eax
	mov eax, 342608305
	mov DWORD PTR [edi+380], eax
	mov eax, -1713440714
	mov DWORD PTR [edi+384], eax
	mov eax, -1
	mov DWORD PTR [edi+388], eax
	mov eax, -1
	mov DWORD PTR [edi+392], eax
	mov eax, -1
	mov DWORD PTR [edi+396], eax
	mov eax, 0
	mov DWORD PTR [edi+400], eax
	mov eax, 0
	mov DWORD PTR [edi+404], eax
	mov eax, 0
	mov DWORD PTR [edi+408], eax
	mov eax, 0
	mov DWORD PTR [edi+412], eax
	mov eax, 0
	mov DWORD PTR [edi+416], eax
	mov eax, 0
	mov DWORD PTR [edi+420], eax
	mov eax, 1
	mov DWORD PTR [edi+424], eax
	mov eax, 0
	mov DWORD PTR [edi+428], eax
	mov eax, 1
	mov DWORD PTR [edi+432], eax
	mov eax, 0
	mov DWORD PTR [edi+436], eax
	mov eax, 0
	mov DWORD PTR [edi+440], eax
	mov eax, 0
	mov DWORD PTR [edi+444], eax
	mov eax, 0
	mov DWORD PTR [edi+448], eax
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov eax, 0
	mov DWORD PTR [edi+456], eax
	mov eax, 0
	mov DWORD PTR [edi+460], eax
	mov eax, 0
	mov DWORD PTR [edi+464], eax
	mov eax, 0
	mov DWORD PTR [edi+468], eax
	mov eax, -1
	mov DWORD PTR [edi+1120], eax
	mov eax, 1
	mov DWORD PTR [edi+1000], eax
	mov eax, 0
	mov DWORD PTR [edi+1004], eax
	mov eax, 2
	mov DWORD PTR [edi+1008], eax
	mov eax, 0
	mov DWORD PTR [edi+1012], eax
	mov eax, 1
	mov DWORD PTR [edi+1016], eax
	mov eax, 0
	mov DWORD PTR [edi+1020], eax
	mov eax, -1495057768
	mov DWORD PTR [edi+1024], eax
	mov eax, 1658446854
	mov DWORD PTR [edi+1028], eax
	mov eax, 419916514
	mov DWORD PTR [edi+1032], eax
	mov eax, 1921109426
	mov DWORD PTR [edi+1036], eax
	mov eax, 1472246065
	mov DWORD PTR [edi+1040], eax
	mov eax, 1942548165
	mov DWORD PTR [edi+1044], eax
	mov ebx, DWORD PTR [esp+8]
	add ebx, 1
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+876], eax
	mov ebx, DWORD PTR [esp+8]
	movzx edx, BYTE PTR [ebx]
	mov DWORD PTR [edi+832], edx
	or edx, 1
	xor edx, 3
	sub edx, 1
	sbb edx, edx
	mov eax, DWORD PTR [edi+1120]
	and eax, edx
	mov DWORD PTR [edi+1120], eax
	mov edx, DWORD PTR [edi+856]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+860]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+864]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+868]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+872]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+876]
	sbb edx, DWORD PTR [edi+84]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+1120]
	and eax, edx
	mov DWORD PTR [edi+1120], eax
	mov eax, 1000
	mov ecx, 856
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 880
	mov ecx, 880
	mov edx, 1048
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 880
	mov ecx, 1048
	mov edx, 1072
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 880
	mov ecx, 208
	mov edx, 1048
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1048
	mov ecx, 1072
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 976
	mov edx, 1072
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 0
	mov DWORD PTR [edi+352], eax
	mov eax, -1073741824
	mov DWORD PTR [edi+356], eax
	mov eax, -1
	mov DWORD PTR [edi+360], eax
	mov eax, -1
	mov DWORD PTR [edi+364], eax
	mov eax, -1
	mov DWORD PTR [edi+368], eax
	mov eax, 1073741823
	mov DWORD PTR [edi+372], eax
	mov esi, 24
20:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+352]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4488], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4489], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4490], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4491], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4492], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4493], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4494], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4495], dl
	test esi, esi
	jne 20b
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+780], eax
	mov esi, 192
21:
	sub esi, 1
	mov eax, 760
	mov ecx, 760
	mov edx, 760
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1072
	mov ecx, 760
	mov edx, 784
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4488]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+760]
	mov edx, DWORD PTR [edi+784]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+764]
	mov edx, DWORD PTR [edi+788]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+768]
	mov edx, DWORD PTR [edi+792]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+772]
	mov edx, DWORD PTR [edi+796]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+776]
	mov edx, DWORD PTR [edi+800]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+780]
	mov edx, DWORD PTR [edi+804]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+780], eax
	test esi, esi
	jne 21b
	mov eax, 160
	mov ecx, 760
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 136
	mov edx, 952
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+928]
	mov ecx, DWORD PTR [edi+832]
	xor ecx, eax
	and ecx, 1
	mov edx, 0
	sub edx, ecx
	mov ecx, edx
	mov eax, DWORD PTR [edi+928]
	mov edx, DWORD PTR [edi+952]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [edi+932]
	mov edx, DWORD PTR [edi+956]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [edi+936]
	mov edx, DWORD PTR [edi+960]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+936], eax
	mov eax, DWORD PTR [edi+940]
	mov edx, DWORD PTR [edi+964]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+940], eax
	mov eax, DWORD PTR [edi+944]
	mov edx, DWORD PTR [edi+968]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+944], eax
	mov eax, DWORD PTR [edi+948]
	mov edx, DWORD PTR [edi+972]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+948], eax
	mov eax, 1000
	mov ecx, 928
	mov edx, 904
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 904
	mov ecx, 904
	mov edx, 1048
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1072
	mov ecx, 1048
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+976]
	or edx, DWORD PTR [edi+980]
	or edx, DWORD PTR [edi+984]
	or edx, DWORD PTR [edi+988]
	or edx, DWORD PTR [edi+992]
	or edx, DWORD PTR [edi+996]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+1120]
	and eax, edx
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+928]
	mov ecx, DWORD PTR [edi+832]
	xor ecx, eax
	and ecx, 1
	mov edx, 0
	sub edx, ecx
	mov ecx, edx
	mov edx, ecx
	add edx, 1
	mov eax, 0
	sub eax, edx
	mov edx, eax
	mov eax, DWORD PTR [edi+1120]
	and eax, edx
	mov DWORD PTR [edi+1120], eax
	mov ecx, DWORD PTR [edi+1120]
	mov ebx, DWORD PTR [esp+4]
	mov eax, 4
	and eax, ecx
	mov BYTE PTR [ebx], al
	mov eax, DWORD PTR [edi+856]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+21], eax
	mov eax, DWORD PTR [edi+860]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+17], eax
	mov eax, DWORD PTR [edi+864]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+13], eax
	mov eax, DWORD PTR [edi+868]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+9], eax
	mov eax, DWORD PTR [edi+872]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+5], eax
	mov eax, DWORD PTR [edi+876]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+1], eax
	mov eax, DWORD PTR [edi+928]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+45], eax
	mov eax, DWORD PTR [edi+932]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+41], eax
	mov eax, DWORD PTR [edi+936]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+37], eax
	mov eax, DWORD PTR [edi+940]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+33], eax
	mov eax, DWORD PTR [edi+944]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+29], eax
	mov eax, DWORD PTR [edi+948]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+25], eax
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	ret
	.p2align 6
