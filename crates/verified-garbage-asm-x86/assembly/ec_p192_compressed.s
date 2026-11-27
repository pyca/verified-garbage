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
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-28]
	movdqu XMMWORD PTR [esp], xmm0
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	lea esp, [esp+28]
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
	mov eax, DWORD PTR [edi+1072]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+1076]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+1080]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+1084]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+1072]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+1076]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+1080]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+1084]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+372], eax
	mov esi, 1
20:
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
	test esi, esi
	jne 20b
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [edi+952], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [edi+956], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+960], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+964], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+968], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+972], eax
	mov eax, 352
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
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+396], eax
	mov eax, 952
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
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+636], eax
	mov eax, 952
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
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+660], eax
	mov eax, 952
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
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+684], eax
	mov eax, 952
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
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+708], eax
	mov eax, 952
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
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+732], eax
	mov eax, 952
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
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [edi+780], eax
	mov esi, 4
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
	test esi, esi
	jne 21b
	mov eax, 736
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
	mov esi, 4
22:
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
	test esi, esi
	jne 22b
	mov eax, 736
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
	mov esi, 4
23:
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
	test esi, esi
	jne 23b
	mov eax, 736
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
	mov esi, 4
24:
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
	test esi, esi
	jne 24b
	mov eax, 736
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
	mov esi, 4
25:
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
	test esi, esi
	jne 25b
	mov eax, 736
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
	mov esi, 4
26:
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
	test esi, esi
	jne 26b
	mov eax, 736
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
	mov esi, 4
27:
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
	test esi, esi
	jne 27b
	mov eax, 736
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
	mov esi, 4
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
	test esi, esi
	jne 28b
	mov eax, 736
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
	mov esi, 4
29:
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
	test esi, esi
	jne 29b
	mov eax, 736
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
	mov esi, 4
210:
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
	test esi, esi
	jne 210b
	mov eax, 736
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
	mov esi, 4
211:
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
	test esi, esi
	jne 211b
	mov eax, 736
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
	mov esi, 4
212:
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
	test esi, esi
	jne 212b
	mov eax, 736
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
	mov esi, 4
213:
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
	test esi, esi
	jne 213b
	mov eax, 736
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
	mov esi, 4
214:
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
	test esi, esi
	jne 214b
	mov eax, 736
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
	mov esi, 4
215:
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
	test esi, esi
	jne 215b
	mov eax, 736
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
	mov esi, 4
216:
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
	test esi, esi
	jne 216b
	mov eax, 736
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
	mov esi, 4
217:
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
	test esi, esi
	jne 217b
	mov eax, 736
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
	mov esi, 4
218:
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
	test esi, esi
	jne 218b
	mov eax, 736
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
	mov esi, 4
219:
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
	test esi, esi
	jne 219b
	mov eax, 736
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
	mov esi, 4
220:
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
	test esi, esi
	jne 220b
	mov eax, 736
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
	mov esi, 4
221:
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
	test esi, esi
	jne 221b
	mov eax, 736
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
	mov esi, 4
222:
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
	test esi, esi
	jne 222b
	mov eax, 736
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
	mov esi, 4
223:
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
	test esi, esi
	jne 223b
	mov eax, 736
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
	mov esi, 4
224:
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
	test esi, esi
	jne 224b
	mov eax, 736
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
	mov esi, 4
225:
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
	test esi, esi
	jne 225b
	mov eax, 736
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
	mov esi, 4
226:
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
	test esi, esi
	jne 226b
	mov eax, 736
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
	mov esi, 4
227:
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
	test esi, esi
	jne 227b
	mov eax, 736
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
	mov esi, 4
228:
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
	test esi, esi
	jne 228b
	mov eax, 736
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
	mov esi, 4
229:
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
	test esi, esi
	jne 229b
	mov eax, 736
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
	mov esi, 4
230:
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
	test esi, esi
	jne 230b
	mov eax, 736
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
	mov esi, 4
231:
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
	test esi, esi
	jne 231b
	mov eax, 736
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
	mov esi, 62
232:
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
	test esi, esi
	jne 232b
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
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-28]
	movdqu XMMWORD PTR [esp], xmm0
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	lea esp, [esp+28]
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
