// The functions of `src/ecdsa_p192.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p192_verify:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+12]
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
	mov esi, 24
20:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+808]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4096], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4097], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4098], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4099], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4100], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4101], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4102], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4103], dl
	test esi, esi
	jne 20b
	mov esi, 24
21:
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
	mov BYTE PTR [ebx+4292], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4293], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4294], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4295], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4296], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4297], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4298], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4299], dl
	test esi, esi
	jne 21b
	mov esi, 24
22:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+376]
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
	jne 22b
	mov ebx, DWORD PTR [esp+12]
	add ebx, 24
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+804], eax
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
	mov ebx, DWORD PTR [esp+4]
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
	mov ebx, DWORD PTR [esp+4]
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
	mov edx, DWORD PTR [edi+808]
	sub edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+812]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+816]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+820]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+824]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+828]
	sbb edx, DWORD PTR [edi+108]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+808]
	or edx, DWORD PTR [edi+812]
	or edx, DWORD PTR [edi+816]
	or edx, DWORD PTR [edi+820]
	or edx, DWORD PTR [edi+824]
	or edx, DWORD PTR [edi+828]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+1120]
	and eax, edx
	mov DWORD PTR [edi+1120], eax
	mov edx, DWORD PTR [edi+784]
	sub edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+788]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+792]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+796]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+800]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+804]
	sbb edx, DWORD PTR [edi+108]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+784]
	or edx, DWORD PTR [edi+788]
	or edx, DWORD PTR [edi+792]
	or edx, DWORD PTR [edi+796]
	or edx, DWORD PTR [edi+800]
	or edx, DWORD PTR [edi+804]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+1120]
	and eax, edx
	mov DWORD PTR [edi+1120], eax
	mov eax, 304
	mov ecx, 784
	mov edx, 952
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+780], eax
	mov esi, 192
23:
	sub esi, 1
	mov eax, 760
	mov ecx, 760
	mov edx, 760
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 952
	mov ecx, 760
	mov edx, 784
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
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
	jne 23b
	mov eax, 304
	mov ecx, 832
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 304
	mov ecx, 808
	mov edx, 1000
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 760
	mov ecx, 1024
	mov edx, 1048
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 760
	mov ecx, 1000
	mov edx, 1072
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 160
	mov ecx, 1048
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 160
	mov ecx, 1072
	mov edx, 904
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 24
24:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+880]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4096], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4097], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4098], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4099], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4100], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4101], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4102], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4103], dl
	test esi, esi
	jne 24b
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3580], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3584], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3588], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3592], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3596], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3600], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3604], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3608], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3612], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3616], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3620], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3624], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3628], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3632], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3636], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3640], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3644], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3648], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3652], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3656], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3660], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3664], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3668], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3672], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3676], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3680], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3684], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3688], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3692], eax
	mov esi, 192
25:
	sub esi, 1
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3572], eax
	push edi
	call {vg_p192_point_double}
	pop eax
	mov edi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+3572], eax
	push edi
	call {vg_p192_point_add}
	pop eax
	mov edi, DWORD PTR [esp+16]
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4096]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+3504]
	mov edx, DWORD PTR [edi+3432]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3508]
	mov edx, DWORD PTR [edi+3436]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3512]
	mov edx, DWORD PTR [edi+3440]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3516]
	mov edx, DWORD PTR [edi+3444]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3448]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3452]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3456]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3460]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3464]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3468]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3472]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3476]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3480]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3484]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3488]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3492]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3496]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3500]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+468], eax
	test esi, esi
	jne 25b
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+952], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+956], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+960], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+964], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+968], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+972], eax
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
	mov esi, 24
26:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+904]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4096], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4097], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4098], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4099], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4100], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4101], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4102], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4103], dl
	test esi, esi
	jne 26b
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [edi+3580], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [edi+3584], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [edi+3588], eax
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [edi+3592], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [edi+3596], eax
	mov eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+3600], eax
	mov eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+3604], eax
	mov eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+3608], eax
	mov eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+3612], eax
	mov eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+3616], eax
	mov eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+3620], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3624], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3628], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3632], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3636], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3640], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3644], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3648], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3652], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3656], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3660], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3664], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3668], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3672], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3676], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3680], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3684], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3688], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3692], eax
	mov esi, 192
27:
	sub esi, 1
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3572], eax
	push edi
	call {vg_p192_point_double}
	pop eax
	mov edi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+3572], eax
	push edi
	call {vg_p192_point_add}
	pop eax
	mov edi, DWORD PTR [esp+16]
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4096]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+3504]
	mov edx, DWORD PTR [edi+3432]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3508]
	mov edx, DWORD PTR [edi+3436]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3512]
	mov edx, DWORD PTR [edi+3440]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3516]
	mov edx, DWORD PTR [edi+3444]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3448]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3452]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3456]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3460]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3464]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3468]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3472]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3476]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3480]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3484]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3488]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3492]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3496]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3500]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+468], eax
	test esi, esi
	jne 27b
	mov eax, 400
	mov ecx, 1048
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 424
	mov ecx, 1072
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 952
	mov edx, 664
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
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 424
	mov ecx, 400
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 688
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 616
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 688
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 952
	mov ecx, 1048
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 400
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 712
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 616
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 712
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 952
	mov ecx, 1072
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 424
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 472
	mov ecx, 736
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 640
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 472
	mov ecx, 736
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 208
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 232
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 472
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 640
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 640
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 472
	mov edx, 496
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 616
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 208
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 232
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 616
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 208
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 712
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 640
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 496
	mov edx, 496
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 736
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 472
	mov ecx, 688
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 472
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 688
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 736
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 520
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [edi+468], eax
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
28:
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
	mov eax, 448
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
	movzx eax, BYTE PTR [eax+4292]
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
	jne 28b
	mov eax, 760
	mov ecx, 400
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
	mov eax, 160
	mov ecx, 880
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
	mov eax, 304
	mov ecx, 904
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1000
	mov ecx, 976
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+448]
	or edx, DWORD PTR [edi+452]
	or edx, DWORD PTR [edi+456]
	or edx, DWORD PTR [edi+460]
	or edx, DWORD PTR [edi+464]
	or edx, DWORD PTR [edi+468]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+1120]
	and eax, edx
	mov DWORD PTR [edi+1120], eax
	mov edx, DWORD PTR [edi+1024]
	or edx, DWORD PTR [edi+1028]
	or edx, DWORD PTR [edi+1032]
	or edx, DWORD PTR [edi+1036]
	or edx, DWORD PTR [edi+1040]
	or edx, DWORD PTR [edi+1044]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+1120]
	and eax, edx
	mov DWORD PTR [edi+1120], eax
	mov ecx, DWORD PTR [edi+1120]
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	ret
	.p2align 6

vg_ecdsa_p192_sign:
	mov ecx, DWORD PTR [esp+24]
	mov ecx, DWORD PTR [ecx+12]
	cmp ecx, 0
	je 20f
	cmp ecx, 1
	je 22f
	cmp ecx, 2
	je 24f
	cmp ecx, 3
	je 26f
	cmp ecx, 4
	je 28f
	cmp ecx, 5
	je 210f
	cmp ecx, 6
	je 212f
	lea esp, [esp-196]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+208]
	mov eax, DWORD PTR [esi+20]
	bswap eax
	mov DWORD PTR [esp+148], eax
	sub eax, -1261295567
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esi+16]
	bswap eax
	mov DWORD PTR [esp+144], eax
	sbb eax, 342608305
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [esp+140], eax
	sbb eax, -1713440714
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [esp+136], eax
	sbb eax, -1
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [esp+132], eax
	sbb eax, -1
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [esp+128], eax
	sbb eax, -1
	mov DWORD PTR [esp], eax
	sbb edx, edx
	mov eax, DWORD PTR [esp+148]
	mov ecx, DWORD PTR [esp+20]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+148], eax
	mov eax, DWORD PTR [esp+144]
	mov ecx, DWORD PTR [esp+16]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+144], eax
	mov eax, DWORD PTR [esp+140]
	mov ecx, DWORD PTR [esp+12]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+140], eax
	mov eax, DWORD PTR [esp+136]
	mov ecx, DWORD PTR [esp+8]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+136], eax
	mov eax, DWORD PTR [esp+132]
	mov ecx, DWORD PTR [esp+4]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [esp+128]
	mov ecx, DWORD PTR [esp]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+128], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, 0
	mov BYTE PTR [edi+2288], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esp+132]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [edi+2333], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 81
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 209
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, 1
	mov BYTE PTR [edi+2288], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esp+132]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [edi+2333], eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 81
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 209
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, 8
	mov DWORD PTR [esp+176], eax
214:
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov edi, DWORD PTR [esp+200]
	mov esi, DWORD PTR [esp+204]
	mov edx, DWORD PTR [esp+208]
	mov ecx, esp
	add ecx, 64
	mov ebp, DWORD PTR [esp+216]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_p192_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 215f
	mov edx, 0
	test edx, edx
	jmp 216f
215:
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, 0
	mov BYTE PTR [edi+2288], al
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 33
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 161
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov edx, 1
	test edx, edx
216:
	jne 214b
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
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+196]
	jmp 213f
212:
	lea esp, [esp-196]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+208]
	mov eax, DWORD PTR [esi+20]
	bswap eax
	mov DWORD PTR [esp+148], eax
	sub eax, -1261295567
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esi+16]
	bswap eax
	mov DWORD PTR [esp+144], eax
	sbb eax, 342608305
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [esp+140], eax
	sbb eax, -1713440714
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [esp+136], eax
	sbb eax, -1
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [esp+132], eax
	sbb eax, -1
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [esp+128], eax
	sbb eax, -1
	mov DWORD PTR [esp], eax
	sbb edx, edx
	mov eax, DWORD PTR [esp+148]
	mov ecx, DWORD PTR [esp+20]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+148], eax
	mov eax, DWORD PTR [esp+144]
	mov ecx, DWORD PTR [esp+16]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+144], eax
	mov eax, DWORD PTR [esp+140]
	mov ecx, DWORD PTR [esp+12]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+140], eax
	mov eax, DWORD PTR [esp+136]
	mov ecx, DWORD PTR [esp+8]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+136], eax
	mov eax, DWORD PTR [esp+132]
	mov ecx, DWORD PTR [esp+4]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [esp+128]
	mov ecx, DWORD PTR [esp]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+128], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, 0
	mov BYTE PTR [edi+2284], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esp+132]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [edi+2329], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 77
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 205
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, 1
	mov BYTE PTR [edi+2284], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esp+132]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [edi+2329], eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 77
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 205
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, 8
	mov DWORD PTR [esp+176], eax
217:
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov edi, DWORD PTR [esp+200]
	mov esi, DWORD PTR [esp+204]
	mov edx, DWORD PTR [esp+208]
	mov ecx, esp
	add ecx, 64
	mov ebp, DWORD PTR [esp+216]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_p192_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 218f
	mov edx, 0
	test edx, edx
	jmp 219f
218:
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, 0
	mov BYTE PTR [edi+2284], al
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 29
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 157
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov edx, 1
	test edx, edx
219:
	jne 217b
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
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+196]
213:
	jmp 211f
210:
	lea esp, [esp-196]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+208]
	mov eax, DWORD PTR [esi+20]
	bswap eax
	mov DWORD PTR [esp+148], eax
	sub eax, -1261295567
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esi+16]
	bswap eax
	mov DWORD PTR [esp+144], eax
	sbb eax, 342608305
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [esp+140], eax
	sbb eax, -1713440714
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [esp+136], eax
	sbb eax, -1
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [esp+132], eax
	sbb eax, -1
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [esp+128], eax
	sbb eax, -1
	mov DWORD PTR [esp], eax
	sbb edx, edx
	mov eax, DWORD PTR [esp+148]
	mov ecx, DWORD PTR [esp+20]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+148], eax
	mov eax, DWORD PTR [esp+144]
	mov ecx, DWORD PTR [esp+16]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+144], eax
	mov eax, DWORD PTR [esp+140]
	mov ecx, DWORD PTR [esp+12]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+140], eax
	mov eax, DWORD PTR [esp+136]
	mov ecx, DWORD PTR [esp+8]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+136], eax
	mov eax, DWORD PTR [esp+132]
	mov ecx, DWORD PTR [esp+4]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [esp+128]
	mov ecx, DWORD PTR [esp]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+128], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [edi+2300], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [edi+2304], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [edi+2308], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [edi+2312], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [edi+2316], eax
	mov eax, 0
	mov BYTE PTR [edi+2320], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esp+132]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [edi+2365], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 113
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 241
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+60], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+116], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+124], eax
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [edi+2300], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [edi+2304], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [edi+2308], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [edi+2312], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [edi+2316], eax
	mov eax, 1
	mov BYTE PTR [edi+2320], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esp+132]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [edi+2365], eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 113
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 241
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+60], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+116], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+124], eax
	mov eax, 8
	mov DWORD PTR [esp+176], eax
220:
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+116], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+124], eax
	mov edi, DWORD PTR [esp+200]
	mov esi, DWORD PTR [esp+204]
	mov edx, DWORD PTR [esp+208]
	mov ecx, esp
	add ecx, 64
	mov ebp, DWORD PTR [esp+216]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_p192_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 221f
	mov edx, 0
	test edx, edx
	jmp 222f
221:
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [edi+2300], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [edi+2304], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [edi+2308], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [edi+2312], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [edi+2316], eax
	mov eax, 0
	mov BYTE PTR [edi+2320], al
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 65
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 193
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+60], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+116], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+124], eax
	mov edx, 1
	test edx, edx
222:
	jne 220b
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
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+196]
211:
	jmp 29f
28:
	lea esp, [esp-196]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+208]
	mov eax, DWORD PTR [esi+20]
	bswap eax
	mov DWORD PTR [esp+148], eax
	sub eax, -1261295567
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esi+16]
	bswap eax
	mov DWORD PTR [esp+144], eax
	sbb eax, 342608305
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [esp+140], eax
	sbb eax, -1713440714
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [esp+136], eax
	sbb eax, -1
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [esp+132], eax
	sbb eax, -1
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [esp+128], eax
	sbb eax, -1
	mov DWORD PTR [esp], eax
	sbb edx, edx
	mov eax, DWORD PTR [esp+148]
	mov ecx, DWORD PTR [esp+20]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+148], eax
	mov eax, DWORD PTR [esp+144]
	mov ecx, DWORD PTR [esp+16]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+144], eax
	mov eax, DWORD PTR [esp+140]
	mov ecx, DWORD PTR [esp+12]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+140], eax
	mov eax, DWORD PTR [esp+136]
	mov ecx, DWORD PTR [esp+8]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+136], eax
	mov eax, DWORD PTR [esp+132]
	mov ecx, DWORD PTR [esp+4]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [esp+128]
	mov ecx, DWORD PTR [esp]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+128], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [edi+2300], eax
	mov eax, 0
	mov BYTE PTR [edi+2304], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esp+132]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [edi+2349], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 97
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 225
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 48
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+44], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 48
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 48
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [edi+2300], eax
	mov eax, 1
	mov BYTE PTR [edi+2304], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esp+132]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [edi+2349], eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 97
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 225
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 48
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+44], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 48
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 48
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov eax, 8
	mov DWORD PTR [esp+176], eax
223:
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 48
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 48
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov edi, DWORD PTR [esp+200]
	mov esi, DWORD PTR [esp+204]
	mov edx, DWORD PTR [esp+208]
	mov ecx, esp
	add ecx, 64
	mov ebp, DWORD PTR [esp+216]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_p192_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 224f
	mov edx, 0
	test edx, edx
	jmp 225f
224:
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [edi+2300], eax
	mov eax, 0
	mov BYTE PTR [edi+2304], al
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 49
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 177
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 48
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+44], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 48
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 48
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov edx, 1
	test edx, edx
225:
	jne 223b
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
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+196]
29:
	jmp 27f
26:
	lea esp, [esp-196]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+208]
	mov eax, DWORD PTR [esi+20]
	bswap eax
	mov DWORD PTR [esp+148], eax
	sub eax, -1261295567
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esi+16]
	bswap eax
	mov DWORD PTR [esp+144], eax
	sbb eax, 342608305
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [esp+140], eax
	sbb eax, -1713440714
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [esp+136], eax
	sbb eax, -1
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [esp+132], eax
	sbb eax, -1
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [esp+128], eax
	sbb eax, -1
	mov DWORD PTR [esp], eax
	sbb edx, edx
	mov eax, DWORD PTR [esp+148]
	mov ecx, DWORD PTR [esp+20]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+148], eax
	mov eax, DWORD PTR [esp+144]
	mov ecx, DWORD PTR [esp+16]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+144], eax
	mov eax, DWORD PTR [esp+140]
	mov ecx, DWORD PTR [esp+12]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+140], eax
	mov eax, DWORD PTR [esp+136]
	mov ecx, DWORD PTR [esp+8]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+136], eax
	mov eax, DWORD PTR [esp+132]
	mov ecx, DWORD PTR [esp+4]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [esp+128]
	mov ecx, DWORD PTR [esp]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+128], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, 0
	mov BYTE PTR [edi+2288], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esp+132]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [edi+2333], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 81
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 145
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, 1
	mov BYTE PTR [edi+2288], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esp+132]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [edi+2333], eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 81
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 145
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, 8
	mov DWORD PTR [esp+176], eax
226:
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov edi, DWORD PTR [esp+200]
	mov esi, DWORD PTR [esp+204]
	mov edx, DWORD PTR [esp+208]
	mov ecx, esp
	add ecx, 64
	mov ebp, DWORD PTR [esp+216]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_p192_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 227f
	mov edx, 0
	test edx, edx
	jmp 228f
227:
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, 0
	mov BYTE PTR [edi+2288], al
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 33
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 97
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov edx, 1
	test edx, edx
228:
	jne 226b
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
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+196]
27:
	jmp 25f
24:
	lea esp, [esp-196]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+208]
	mov eax, DWORD PTR [esi+20]
	bswap eax
	mov DWORD PTR [esp+148], eax
	sub eax, -1261295567
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esi+16]
	bswap eax
	mov DWORD PTR [esp+144], eax
	sbb eax, 342608305
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [esp+140], eax
	sbb eax, -1713440714
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [esp+136], eax
	sbb eax, -1
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [esp+132], eax
	sbb eax, -1
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [esp+128], eax
	sbb eax, -1
	mov DWORD PTR [esp], eax
	sbb edx, edx
	mov eax, DWORD PTR [esp+148]
	mov ecx, DWORD PTR [esp+20]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+148], eax
	mov eax, DWORD PTR [esp+144]
	mov ecx, DWORD PTR [esp+16]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+144], eax
	mov eax, DWORD PTR [esp+140]
	mov ecx, DWORD PTR [esp+12]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+140], eax
	mov eax, DWORD PTR [esp+136]
	mov ecx, DWORD PTR [esp+8]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+136], eax
	mov eax, DWORD PTR [esp+132]
	mov ecx, DWORD PTR [esp+4]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [esp+128]
	mov ecx, DWORD PTR [esp]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+128], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, 0
	mov BYTE PTR [edi+2284], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esp+132]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [edi+2329], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 77
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 141
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, 1
	mov BYTE PTR [edi+2284], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esp+132]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [edi+2329], eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 77
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 141
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, 8
	mov DWORD PTR [esp+176], eax
229:
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov edi, DWORD PTR [esp+200]
	mov esi, DWORD PTR [esp+204]
	mov edx, DWORD PTR [esp+208]
	mov ecx, esp
	add ecx, 64
	mov ebp, DWORD PTR [esp+216]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_p192_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 230f
	mov edx, 0
	test edx, edx
	jmp 231f
230:
	mov edi, DWORD PTR [esp+216]
	mov esi, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, 0
	mov BYTE PTR [edi+2284], al
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 2256
	mov ecx, 29
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 93
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 0
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+216]
	add ebx, 256
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+216]
	add edx, 1152
	mov ebp, DWORD PTR [esp+216]
	add ebp, 512
	mov esi, DWORD PTR [esp+220]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+216]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov edx, 1
	test edx, edx
231:
	jne 229b
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
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+196]
25:
	jmp 23f
22:
	lea esp, [esp-468]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+480]
	mov edi, DWORD PTR [esp+488]
	mov eax, 0
	mov DWORD PTR [esp+196], eax
	mov DWORD PTR [esp+200], eax
	mov DWORD PTR [esp+204], eax
	mov DWORD PTR [esp+208], eax
	mov DWORD PTR [esp+212], eax
	mov DWORD PTR [esp+216], eax
	mov DWORD PTR [esp+220], eax
	mov DWORD PTR [esp+224], eax
	mov DWORD PTR [esp+228], eax
	mov DWORD PTR [esp+232], eax
	mov DWORD PTR [esp+236], eax
	mov DWORD PTR [esp+240], eax
	mov DWORD PTR [esp+244], eax
	mov DWORD PTR [esp+248], eax
	mov DWORD PTR [esp+252], eax
	mov DWORD PTR [esp+256], eax
	mov DWORD PTR [esp+260], eax
	mov DWORD PTR [esp+264], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+200], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+204], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+208], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+212], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+216], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, 0
	mov BYTE PTR [edi+2276], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2277], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2281], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2321], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 69
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 133
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, 1
	mov BYTE PTR [edi+2276], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2277], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2281], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2321], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 69
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 133
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, 8
	mov DWORD PTR [esp+176], eax
232:
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+340], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+344], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+348], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+352], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+356], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+360], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+364], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+368], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+372], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+376], eax
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 196
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_p192_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 233f
	mov edx, 0
	test edx, edx
	jmp 234f
233:
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, 0
	mov BYTE PTR [edi+2276], al
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 21
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 85
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov edx, 1
	test edx, edx
234:
	jne 232b
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
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+468]
23:
	jmp 21f
20:
	lea esp, [esp-468]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+480]
	mov edi, DWORD PTR [esp+488]
	mov eax, 0
	mov DWORD PTR [esp+196], eax
	mov DWORD PTR [esp+200], eax
	mov DWORD PTR [esp+204], eax
	mov DWORD PTR [esp+208], eax
	mov DWORD PTR [esp+212], eax
	mov DWORD PTR [esp+216], eax
	mov DWORD PTR [esp+220], eax
	mov DWORD PTR [esp+224], eax
	mov DWORD PTR [esp+228], eax
	mov DWORD PTR [esp+232], eax
	mov DWORD PTR [esp+236], eax
	mov DWORD PTR [esp+240], eax
	mov DWORD PTR [esp+244], eax
	mov DWORD PTR [esp+248], eax
	mov DWORD PTR [esp+252], eax
	mov DWORD PTR [esp+256], eax
	mov DWORD PTR [esp+260], eax
	mov DWORD PTR [esp+264], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+204], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+208], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+212], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+216], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, 0
	mov BYTE PTR [edi+2272], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2273], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2277], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2281], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2317], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 65
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 129
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, 1
	mov BYTE PTR [edi+2272], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2273], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2277], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2281], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2317], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 65
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 129
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, 8
	mov DWORD PTR [esp+176], eax
235:
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+340], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+344], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+348], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+352], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+356], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+360], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+364], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+368], eax
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 196
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_p192_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 236f
	mov edx, 0
	test edx, edx
	jmp 237f
236:
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, 0
	mov BYTE PTR [edi+2272], al
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 17
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 81
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov edx, 1
	test edx, edx
237:
	jne 235b
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
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+468]
21:
	ret
	.p2align 6
