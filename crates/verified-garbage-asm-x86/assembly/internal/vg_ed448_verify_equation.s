// The functions of `src/internal/vg_ed448_verify_equation.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_verify_equation:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+8]
	mov ebp, edi
	mov ecx, 57
20:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebp+4608], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebp+4609], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebp+4610], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebp+4611], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebp+4612], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebp+4613], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebp+4614], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebp+4615], dl
	add esi, 1
	add ebp, 8
	sub ecx, 1
	jne 20b
	mov esi, ebx
	add esi, 57
	mov ebp, edi
	mov ecx, 57
21:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebp+3072], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebp+3073], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebp+3074], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebp+3075], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebp+3076], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebp+3077], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebp+3078], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebp+3079], dl
	add esi, 1
	add ebp, 8
	sub ecx, 1
	jne 21b
	sub esi, 114
	mov eax, 0
	mov DWORD PTR [edi+16], eax
	xor ecx, ecx
	mov eax, DWORD PTR [esi+57]
	adc eax, 1420278541
	mov eax, DWORD PTR [esi+61]
	adc eax, -595116691
	mov eax, DWORD PTR [esi+65]
	adc eax, 1916432554
	mov eax, DWORD PTR [esi+69]
	adc eax, -560775795
	mov eax, DWORD PTR [esi+73]
	adc eax, 1361693039
	mov eax, DWORD PTR [esi+77]
	adc eax, 1001465014
	mov eax, DWORD PTR [esi+81]
	adc eax, -2093622250
	mov eax, DWORD PTR [esi+85]
	adc eax, 0
	mov eax, DWORD PTR [esi+89]
	adc eax, 0
	mov eax, DWORD PTR [esi+93]
	adc eax, 0
	mov eax, DWORD PTR [esi+97]
	adc eax, 0
	mov eax, DWORD PTR [esi+101]
	adc eax, 0
	mov eax, DWORD PTR [esi+105]
	adc eax, 0
	mov eax, DWORD PTR [esi+109]
	adc eax, -1073741824
	sbb ecx, ecx
	movzx eax, BYTE PTR [esi+113]
	or eax, ecx
	or eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+16], eax
	mov ebp, edi
	add ebp, 64
	mov ebx, 0
	mov eax, 704
22:
	mov DWORD PTR [ebp], ebx
	add ebp, 4
	sub eax, 1
	jne 22b
	mov ebp, edi
	add ebp, 64
	mov eax, 1
	mov DWORD PTR [ebp+128], eax
	mov eax, 1
	mov DWORD PTR [ebp+256], eax
	mov eax, -955465634
	mov DWORD PTR [ebp+1024], eax
	mov eax, 640067627
	mov DWORD PTR [ebp+1028], eax
	mov eax, -1962896498
	mov DWORD PTR [ebp+1032], eax
	mov eax, 1127973089
	mov DWORD PTR [ebp+1036], eax
	mov eax, 716596497
	mov DWORD PTR [ebp+1040], eax
	mov eax, 313400055
	mov DWORD PTR [ebp+1044], eax
	mov eax, -1546410908
	mov DWORD PTR [ebp+1048], eax
	mov eax, -361897180
	mov DWORD PTR [ebp+1052], eax
	mov eax, 1192171367
	mov DWORD PTR [ebp+1056], eax
	mov eax, -1642830480
	mov DWORD PTR [ebp+1060], eax
	mov eax, 582956762
	mov DWORD PTR [ebp+1064], eax
	mov eax, 572331430
	mov DWORD PTR [ebp+1068], eax
	mov eax, 1810697709
	mov DWORD PTR [ebp+1072], eax
	mov eax, 1327067334
	mov DWORD PTR [ebp+1076], eax
	mov eax, -231671276
	mov DWORD PTR [ebp+1152], eax
	mov eax, -1744275109
	mov DWORD PTR [ebp+1156], eax
	mov eax, 1322764461
	mov DWORD PTR [ebp+1160], eax
	mov eax, -37940436
	mov DWORD PTR [ebp+1164], eax
	mov eax, -428066364
	mov DWORD PTR [ebp+1168], eax
	mov eax, 986971932
	mov DWORD PTR [ebp+1172], eax
	mov eax, 94421719
	mov DWORD PTR [ebp+1176], eax
	mov eax, -2022138850
	mov DWORD PTR [ebp+1180], eax
	mov eax, 1822660672
	mov DWORD PTR [ebp+1184], eax
	mov eax, 1273656179
	mov DWORD PTR [ebp+1188], eax
	mov eax, 1456064354
	mov DWORD PTR [ebp+1192], eax
	mov eax, -2005524425
	mov DWORD PTR [ebp+1196], eax
	mov eax, 1857469476
	mov DWORD PTR [ebp+1200], eax
	mov eax, 1765754481
	mov DWORD PTR [ebp+1204], eax
	mov eax, 1
	mov DWORD PTR [ebp+1280], eax
	mov eax, -39082
	mov DWORD PTR [ebp+1408], eax
	mov eax, -1
	mov DWORD PTR [ebp+1412], eax
	mov eax, -1
	mov DWORD PTR [ebp+1416], eax
	mov eax, -1
	mov DWORD PTR [ebp+1420], eax
	mov eax, -1
	mov DWORD PTR [ebp+1424], eax
	mov eax, -1
	mov DWORD PTR [ebp+1428], eax
	mov eax, -1
	mov DWORD PTR [ebp+1432], eax
	mov eax, -2
	mov DWORD PTR [ebp+1436], eax
	mov eax, -1
	mov DWORD PTR [ebp+1440], eax
	mov eax, -1
	mov DWORD PTR [ebp+1444], eax
	mov eax, -1
	mov DWORD PTR [ebp+1448], eax
	mov eax, -1
	mov DWORD PTR [ebp+1452], eax
	mov eax, -1
	mov DWORD PTR [ebp+1456], eax
	mov eax, -1
	mov DWORD PTR [ebp+1460], eax
	mov esi, DWORD PTR [esp+8]
	mov DWORD PTR [edi+4352], esi
	mov ebx, 2
	mov DWORD PTR [edi+4356], ebx
23:
	mov eax, DWORD PTR [edi+832]
	mov DWORD PTR [edi+4096], eax
	mov eax, DWORD PTR [edi+836]
	mov DWORD PTR [edi+4100], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+4104], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+4108], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+4112], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+4116], eax
	mov eax, DWORD PTR [edi+856]
	mov DWORD PTR [edi+4120], eax
	mov eax, DWORD PTR [edi+860]
	mov DWORD PTR [edi+4124], eax
	mov eax, DWORD PTR [edi+864]
	mov DWORD PTR [edi+4128], eax
	mov eax, DWORD PTR [edi+868]
	mov DWORD PTR [edi+4132], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+4136], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+4140], eax
	mov eax, DWORD PTR [edi+880]
	mov DWORD PTR [edi+4144], eax
	mov eax, DWORD PTR [edi+884]
	mov DWORD PTR [edi+4148], eax
	mov eax, DWORD PTR [edi+960]
	mov DWORD PTR [edi+4224], eax
	mov eax, DWORD PTR [edi+964]
	mov DWORD PTR [edi+4228], eax
	mov eax, DWORD PTR [edi+968]
	mov DWORD PTR [edi+4232], eax
	mov eax, DWORD PTR [edi+972]
	mov DWORD PTR [edi+4236], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [edi+4240], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [edi+4244], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [edi+4248], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [edi+4252], eax
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [edi+4256], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [edi+4260], eax
	mov eax, DWORD PTR [edi+1000]
	mov DWORD PTR [edi+4264], eax
	mov eax, DWORD PTR [edi+1004]
	mov DWORD PTR [edi+4268], eax
	mov eax, DWORD PTR [edi+1008]
	mov DWORD PTR [edi+4272], eax
	mov eax, DWORD PTR [edi+1012]
	mov DWORD PTR [edi+4276], eax
	mov esi, DWORD PTR [edi+4352]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+960], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+964], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+968], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+972], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1012], eax
	movzx eax, BYTE PTR [esi+56]
	mov edx, eax
	shr edx, 7
	mov DWORD PTR [edi+20], edx
	and eax, 127
	or eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+960]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+964]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+968]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+972]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+1000]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+1004]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+1008]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+1012]
	mov DWORD PTR [edi+244], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+192]
	adc eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	adc eax, 0
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	adc eax, 0
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	adc eax, 0
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	adc eax, 0
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	adc eax, 0
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	adc eax, 0
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	adc eax, 1
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	adc eax, 0
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	adc eax, 0
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	adc eax, 0
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	adc eax, 0
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	adc eax, 0
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	adc eax, 0
	mov DWORD PTR [edi+3892], eax
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+3840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+3844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+3848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+3852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+3856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+3860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+3864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+3868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+3872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+3876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+3880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+3884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+3888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+3892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov ecx, 0
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [edi+960]
	or ecx, eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [edi+964]
	or ecx, eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [edi+968]
	or ecx, eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [edi+972]
	or ecx, eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [edi+976]
	or ecx, eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [edi+980]
	or ecx, eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [edi+984]
	or ecx, eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [edi+988]
	or ecx, eax
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [edi+992]
	or ecx, eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [edi+996]
	or ecx, eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [edi+1000]
	or ecx, eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [edi+1004]
	or ecx, eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [edi+1008]
	or ecx, eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [edi+1012]
	or ecx, eax
	or ecx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+16], ecx
	mov eax, 1600
	mov ecx, 960
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1600
	mov edx, 1344
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 1472
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 448
	mov edx, 1344
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 1728
	mov edx, 448
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 576
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 1728
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 704
	mov edx, 1728
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 704
	mov edx, 448
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 832
	mov edx, 576
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1600]
	mov DWORD PTR [edi+1856], eax
	mov eax, DWORD PTR [edi+1604]
	mov DWORD PTR [edi+1860], eax
	mov eax, DWORD PTR [edi+1608]
	mov DWORD PTR [edi+1864], eax
	mov eax, DWORD PTR [edi+1612]
	mov DWORD PTR [edi+1868], eax
	mov eax, DWORD PTR [edi+1616]
	mov DWORD PTR [edi+1872], eax
	mov eax, DWORD PTR [edi+1620]
	mov DWORD PTR [edi+1876], eax
	mov eax, DWORD PTR [edi+1624]
	mov DWORD PTR [edi+1880], eax
	mov eax, DWORD PTR [edi+1628]
	mov DWORD PTR [edi+1884], eax
	mov eax, DWORD PTR [edi+1632]
	mov DWORD PTR [edi+1888], eax
	mov eax, DWORD PTR [edi+1636]
	mov DWORD PTR [edi+1892], eax
	mov eax, DWORD PTR [edi+1640]
	mov DWORD PTR [edi+1896], eax
	mov eax, DWORD PTR [edi+1644]
	mov DWORD PTR [edi+1900], eax
	mov eax, DWORD PTR [edi+1648]
	mov DWORD PTR [edi+1904], eax
	mov eax, DWORD PTR [edi+1652]
	mov DWORD PTR [edi+1908], eax
	mov esi, 1
24:
	mov eax, 1856
	mov ecx, 1856
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 24b
	mov eax, 1856
	mov ecx, 1856
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1856]
	mov DWORD PTR [edi+1984], eax
	mov eax, DWORD PTR [edi+1860]
	mov DWORD PTR [edi+1988], eax
	mov eax, DWORD PTR [edi+1864]
	mov DWORD PTR [edi+1992], eax
	mov eax, DWORD PTR [edi+1868]
	mov DWORD PTR [edi+1996], eax
	mov eax, DWORD PTR [edi+1872]
	mov DWORD PTR [edi+2000], eax
	mov eax, DWORD PTR [edi+1876]
	mov DWORD PTR [edi+2004], eax
	mov eax, DWORD PTR [edi+1880]
	mov DWORD PTR [edi+2008], eax
	mov eax, DWORD PTR [edi+1884]
	mov DWORD PTR [edi+2012], eax
	mov eax, DWORD PTR [edi+1888]
	mov DWORD PTR [edi+2016], eax
	mov eax, DWORD PTR [edi+1892]
	mov DWORD PTR [edi+2020], eax
	mov eax, DWORD PTR [edi+1896]
	mov DWORD PTR [edi+2024], eax
	mov eax, DWORD PTR [edi+1900]
	mov DWORD PTR [edi+2028], eax
	mov eax, DWORD PTR [edi+1904]
	mov DWORD PTR [edi+2032], eax
	mov eax, DWORD PTR [edi+1908]
	mov DWORD PTR [edi+2036], eax
	mov esi, 2
25:
	mov eax, 1984
	mov ecx, 1984
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 25b
	mov eax, 1984
	mov ecx, 1984
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1984]
	mov DWORD PTR [edi+2112], eax
	mov eax, DWORD PTR [edi+1988]
	mov DWORD PTR [edi+2116], eax
	mov eax, DWORD PTR [edi+1992]
	mov DWORD PTR [edi+2120], eax
	mov eax, DWORD PTR [edi+1996]
	mov DWORD PTR [edi+2124], eax
	mov eax, DWORD PTR [edi+2000]
	mov DWORD PTR [edi+2128], eax
	mov eax, DWORD PTR [edi+2004]
	mov DWORD PTR [edi+2132], eax
	mov eax, DWORD PTR [edi+2008]
	mov DWORD PTR [edi+2136], eax
	mov eax, DWORD PTR [edi+2012]
	mov DWORD PTR [edi+2140], eax
	mov eax, DWORD PTR [edi+2016]
	mov DWORD PTR [edi+2144], eax
	mov eax, DWORD PTR [edi+2020]
	mov DWORD PTR [edi+2148], eax
	mov eax, DWORD PTR [edi+2024]
	mov DWORD PTR [edi+2152], eax
	mov eax, DWORD PTR [edi+2028]
	mov DWORD PTR [edi+2156], eax
	mov eax, DWORD PTR [edi+2032]
	mov DWORD PTR [edi+2160], eax
	mov eax, DWORD PTR [edi+2036]
	mov DWORD PTR [edi+2164], eax
	mov esi, 4
26:
	mov eax, 2112
	mov ecx, 2112
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 26b
	mov eax, 2112
	mov ecx, 2112
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2112]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2116]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2120]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2124]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2128]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2132]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2136]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2140]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2144]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2148]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2292], eax
	mov esi, 8
27:
	mov eax, 2240
	mov ecx, 2240
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 27b
	mov eax, 2240
	mov ecx, 2240
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2240]
	mov DWORD PTR [edi+2368], eax
	mov eax, DWORD PTR [edi+2244]
	mov DWORD PTR [edi+2372], eax
	mov eax, DWORD PTR [edi+2248]
	mov DWORD PTR [edi+2376], eax
	mov eax, DWORD PTR [edi+2252]
	mov DWORD PTR [edi+2380], eax
	mov eax, DWORD PTR [edi+2256]
	mov DWORD PTR [edi+2384], eax
	mov eax, DWORD PTR [edi+2260]
	mov DWORD PTR [edi+2388], eax
	mov eax, DWORD PTR [edi+2264]
	mov DWORD PTR [edi+2392], eax
	mov eax, DWORD PTR [edi+2268]
	mov DWORD PTR [edi+2396], eax
	mov eax, DWORD PTR [edi+2272]
	mov DWORD PTR [edi+2400], eax
	mov eax, DWORD PTR [edi+2276]
	mov DWORD PTR [edi+2404], eax
	mov eax, DWORD PTR [edi+2280]
	mov DWORD PTR [edi+2408], eax
	mov eax, DWORD PTR [edi+2284]
	mov DWORD PTR [edi+2412], eax
	mov eax, DWORD PTR [edi+2288]
	mov DWORD PTR [edi+2416], eax
	mov eax, DWORD PTR [edi+2292]
	mov DWORD PTR [edi+2420], eax
	mov esi, 16
28:
	mov eax, 2368
	mov ecx, 2368
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 28b
	mov eax, 2368
	mov ecx, 2368
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2368]
	mov DWORD PTR [edi+2496], eax
	mov eax, DWORD PTR [edi+2372]
	mov DWORD PTR [edi+2500], eax
	mov eax, DWORD PTR [edi+2376]
	mov DWORD PTR [edi+2504], eax
	mov eax, DWORD PTR [edi+2380]
	mov DWORD PTR [edi+2508], eax
	mov eax, DWORD PTR [edi+2384]
	mov DWORD PTR [edi+2512], eax
	mov eax, DWORD PTR [edi+2388]
	mov DWORD PTR [edi+2516], eax
	mov eax, DWORD PTR [edi+2392]
	mov DWORD PTR [edi+2520], eax
	mov eax, DWORD PTR [edi+2396]
	mov DWORD PTR [edi+2524], eax
	mov eax, DWORD PTR [edi+2400]
	mov DWORD PTR [edi+2528], eax
	mov eax, DWORD PTR [edi+2404]
	mov DWORD PTR [edi+2532], eax
	mov eax, DWORD PTR [edi+2408]
	mov DWORD PTR [edi+2536], eax
	mov eax, DWORD PTR [edi+2412]
	mov DWORD PTR [edi+2540], eax
	mov eax, DWORD PTR [edi+2416]
	mov DWORD PTR [edi+2544], eax
	mov eax, DWORD PTR [edi+2420]
	mov DWORD PTR [edi+2548], eax
	mov esi, 32
29:
	mov eax, 2496
	mov ecx, 2496
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 29b
	mov eax, 2496
	mov ecx, 2496
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2496]
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2500]
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2504]
	mov DWORD PTR [edi+2632], eax
	mov eax, DWORD PTR [edi+2508]
	mov DWORD PTR [edi+2636], eax
	mov eax, DWORD PTR [edi+2512]
	mov DWORD PTR [edi+2640], eax
	mov eax, DWORD PTR [edi+2516]
	mov DWORD PTR [edi+2644], eax
	mov eax, DWORD PTR [edi+2520]
	mov DWORD PTR [edi+2648], eax
	mov eax, DWORD PTR [edi+2524]
	mov DWORD PTR [edi+2652], eax
	mov eax, DWORD PTR [edi+2528]
	mov DWORD PTR [edi+2656], eax
	mov eax, DWORD PTR [edi+2532]
	mov DWORD PTR [edi+2660], eax
	mov eax, DWORD PTR [edi+2536]
	mov DWORD PTR [edi+2664], eax
	mov eax, DWORD PTR [edi+2540]
	mov DWORD PTR [edi+2668], eax
	mov eax, DWORD PTR [edi+2544]
	mov DWORD PTR [edi+2672], eax
	mov eax, DWORD PTR [edi+2548]
	mov DWORD PTR [edi+2676], eax
	mov esi, 64
210:
	mov eax, 2624
	mov ecx, 2624
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 210b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 64
211:
	mov eax, 2624
	mov ecx, 2624
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 211b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 16
212:
	mov eax, 2624
	mov ecx, 2624
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 212b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 8
213:
	mov eax, 2624
	mov ecx, 2624
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 213b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 4
214:
	mov eax, 2624
	mov ecx, 2624
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 214b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 2
215:
	mov eax, 2624
	mov ecx, 2624
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 215b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2624]
	mov DWORD PTR [edi+2752], eax
	mov eax, DWORD PTR [edi+2628]
	mov DWORD PTR [edi+2756], eax
	mov eax, DWORD PTR [edi+2632]
	mov DWORD PTR [edi+2760], eax
	mov eax, DWORD PTR [edi+2636]
	mov DWORD PTR [edi+2764], eax
	mov eax, DWORD PTR [edi+2640]
	mov DWORD PTR [edi+2768], eax
	mov eax, DWORD PTR [edi+2644]
	mov DWORD PTR [edi+2772], eax
	mov eax, DWORD PTR [edi+2648]
	mov DWORD PTR [edi+2776], eax
	mov eax, DWORD PTR [edi+2652]
	mov DWORD PTR [edi+2780], eax
	mov eax, DWORD PTR [edi+2656]
	mov DWORD PTR [edi+2784], eax
	mov eax, DWORD PTR [edi+2660]
	mov DWORD PTR [edi+2788], eax
	mov eax, DWORD PTR [edi+2664]
	mov DWORD PTR [edi+2792], eax
	mov eax, DWORD PTR [edi+2668]
	mov DWORD PTR [edi+2796], eax
	mov eax, DWORD PTR [edi+2672]
	mov DWORD PTR [edi+2800], eax
	mov eax, DWORD PTR [edi+2676]
	mov DWORD PTR [edi+2804], eax
	mov esi, 1
216:
	mov eax, 2752
	mov ecx, 2752
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 216b
	mov eax, 2752
	mov ecx, 2752
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 223
217:
	mov eax, 2752
	mov ecx, 2752
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 217b
	mov eax, 2752
	mov ecx, 2752
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 832
	mov edx, 2752
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 832
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 448
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1600]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+1604]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+1608]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+1612]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+1616]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+1620]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+1624]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+1628]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+1632]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+1636]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+1640]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+1644]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+1648]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+1652]
	mov DWORD PTR [edi+244], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+192]
	adc eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	adc eax, 0
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	adc eax, 0
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	adc eax, 0
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	adc eax, 0
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	adc eax, 0
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	adc eax, 0
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	adc eax, 1
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	adc eax, 0
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	adc eax, 0
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	adc eax, 0
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	adc eax, 0
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	adc eax, 0
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	adc eax, 0
	mov DWORD PTR [edi+3892], eax
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+3840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+3844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+3848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+3852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+3856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+3860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+3864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+3868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+3872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+3876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+3880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+3884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+3888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+3892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+1600], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+1604], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+1608], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+1612], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+1616], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+1620], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+1624], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+1628], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+1632], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+1636], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+1640], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+1644], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+1648], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+1652], eax
	mov eax, DWORD PTR [edi+1728]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+1732]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+1736]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+1740]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+1744]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+1748]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+1752]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+244], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+192]
	adc eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	adc eax, 0
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	adc eax, 0
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	adc eax, 0
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	adc eax, 0
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	adc eax, 0
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	adc eax, 0
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	adc eax, 1
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	adc eax, 0
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	adc eax, 0
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	adc eax, 0
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	adc eax, 0
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	adc eax, 0
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	adc eax, 0
	mov DWORD PTR [edi+3892], eax
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+3840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+3844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+3848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+3852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+3856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+3860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+3864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+3868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+3872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+3876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+3880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+3884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+3888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+3892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov ecx, 0
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [edi+1600]
	or ecx, eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [edi+1604]
	or ecx, eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [edi+1608]
	or ecx, eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [edi+1612]
	or ecx, eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [edi+1616]
	or ecx, eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [edi+1620]
	or ecx, eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [edi+1624]
	or ecx, eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [edi+1628]
	or ecx, eax
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [edi+1632]
	or ecx, eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [edi+1636]
	or ecx, eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [edi+1640]
	or ecx, eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [edi+1644]
	or ecx, eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [edi+1648]
	or ecx, eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [edi+1652]
	or ecx, eax
	or ecx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+16], ecx
	mov eax, 1600
	mov ecx, 832
	mov edx, 832
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	mov edx, 832
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+832]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+836]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+856]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+860]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+864]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+868]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+880]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+884]
	mov DWORD PTR [edi+244], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+192]
	adc eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	adc eax, 0
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	adc eax, 0
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	adc eax, 0
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	adc eax, 0
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	adc eax, 0
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	adc eax, 0
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	adc eax, 1
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	adc eax, 0
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	adc eax, 0
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	adc eax, 0
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	adc eax, 0
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	adc eax, 0
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	adc eax, 0
	mov DWORD PTR [edi+3892], eax
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+3840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+3844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+3848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+3852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+3856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+3860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+3864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+3868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+3872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+3876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+3880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+3884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+3888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+3892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov edx, DWORD PTR [edi+192]
	or edx, DWORD PTR [edi+196]
	or edx, DWORD PTR [edi+200]
	or edx, DWORD PTR [edi+204]
	or edx, DWORD PTR [edi+208]
	or edx, DWORD PTR [edi+212]
	or edx, DWORD PTR [edi+216]
	or edx, DWORD PTR [edi+220]
	or edx, DWORD PTR [edi+224]
	or edx, DWORD PTR [edi+228]
	or edx, DWORD PTR [edi+232]
	or edx, DWORD PTR [edi+236]
	or edx, DWORD PTR [edi+240]
	or edx, DWORD PTR [edi+244]
	mov eax, 0
	sub eax, edx
	sbb edx, edx
	add edx, 1
	and edx, DWORD PTR [edi+20]
	or edx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+16], edx
	mov eax, DWORD PTR [edi+192]
	and eax, 1
	xor eax, DWORD PTR [edi+20]
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [edi+832]
	mov ecx, DWORD PTR [edi+1600]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+832], eax
	mov DWORD PTR [edi+1600], ecx
	mov eax, DWORD PTR [edi+836]
	mov ecx, DWORD PTR [edi+1604]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+836], eax
	mov DWORD PTR [edi+1604], ecx
	mov eax, DWORD PTR [edi+840]
	mov ecx, DWORD PTR [edi+1608]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+840], eax
	mov DWORD PTR [edi+1608], ecx
	mov eax, DWORD PTR [edi+844]
	mov ecx, DWORD PTR [edi+1612]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+844], eax
	mov DWORD PTR [edi+1612], ecx
	mov eax, DWORD PTR [edi+848]
	mov ecx, DWORD PTR [edi+1616]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+848], eax
	mov DWORD PTR [edi+1616], ecx
	mov eax, DWORD PTR [edi+852]
	mov ecx, DWORD PTR [edi+1620]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+852], eax
	mov DWORD PTR [edi+1620], ecx
	mov eax, DWORD PTR [edi+856]
	mov ecx, DWORD PTR [edi+1624]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+856], eax
	mov DWORD PTR [edi+1624], ecx
	mov eax, DWORD PTR [edi+860]
	mov ecx, DWORD PTR [edi+1628]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+860], eax
	mov DWORD PTR [edi+1628], ecx
	mov eax, DWORD PTR [edi+864]
	mov ecx, DWORD PTR [edi+1632]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+864], eax
	mov DWORD PTR [edi+1632], ecx
	mov eax, DWORD PTR [edi+868]
	mov ecx, DWORD PTR [edi+1636]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+868], eax
	mov DWORD PTR [edi+1636], ecx
	mov eax, DWORD PTR [edi+872]
	mov ecx, DWORD PTR [edi+1640]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+872], eax
	mov DWORD PTR [edi+1640], ecx
	mov eax, DWORD PTR [edi+876]
	mov ecx, DWORD PTR [edi+1644]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+876], eax
	mov DWORD PTR [edi+1644], ecx
	mov eax, DWORD PTR [edi+880]
	mov ecx, DWORD PTR [edi+1648]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+880], eax
	mov DWORD PTR [edi+1648], ecx
	mov eax, DWORD PTR [edi+884]
	mov ecx, DWORD PTR [edi+1652]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+884], eax
	mov DWORD PTR [edi+1652], ecx
	mov esi, DWORD PTR [esp+4]
	mov DWORD PTR [edi+4352], esi
	mov ebx, DWORD PTR [edi+4356]
	sub ebx, 1
	mov DWORD PTR [edi+4356], ebx
	jne 23b
	mov eax, 832
	mov ecx, 64
	mov edx, 832
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 0
	mov ebx, 0
	mov ecx, 0
	mov eax, edi
218:
	mov ebp, edi
	add ebp, esi
	movzx edx, BYTE PTR [ebp+4608]
	cmp ebx, 0
	je 219f
	xor edx, -1
	add edx, 1
	and edx, ebx
	add ecx, edx
	mov edx, 0
	mov BYTE PTR [ebp+4608], dl
	mov BYTE PTR [eax+4608], cl
	add ebx, ebx
	and ebx, 15
	jmp 220f
219:
	mov ecx, edx
	mov ebx, edx
	add ebx, ebx
	mov eax, ebp
220:
	add esi, 1
	cmp esi, 456
	jne 218b
	mov esi, 0
	mov ebx, 0
	mov ecx, 0
	mov eax, edi
221:
	mov ebp, edi
	add ebp, esi
	movzx edx, BYTE PTR [ebp+3072]
	cmp ebx, 0
	je 222f
	xor edx, -1
	add edx, 1
	and edx, ebx
	add ecx, edx
	mov edx, 0
	mov BYTE PTR [ebp+3072], dl
	mov BYTE PTR [eax+3072], cl
	add ebx, ebx
	and ebx, 127
	jmp 223f
222:
	mov ecx, edx
	mov ebx, edx
	add ebx, ebx
	mov eax, ebp
223:
	add esi, 1
	cmp esi, 456
	jne 221b
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_ED448_B_TABLE}
	pop ecx
	mov DWORD PTR [edi+4360], eax
	mov eax, DWORD PTR [edi+832]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+836]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+856]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+860]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+864]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+868]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+880]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+884]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+960]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+964]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+968]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+972]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+1000]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+1004]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+1008]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+1012]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+1344]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+1348]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+1352]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+1356]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+1360]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+1364]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+1368]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+1372]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+1376]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+1380]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+1384]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+1388]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+1392]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+1396]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+1344]
	mov DWORD PTR [edi+2752], eax
	mov eax, DWORD PTR [edi+1348]
	mov DWORD PTR [edi+2756], eax
	mov eax, DWORD PTR [edi+1352]
	mov DWORD PTR [edi+2760], eax
	mov eax, DWORD PTR [edi+1356]
	mov DWORD PTR [edi+2764], eax
	mov eax, DWORD PTR [edi+1360]
	mov DWORD PTR [edi+2768], eax
	mov eax, DWORD PTR [edi+1364]
	mov DWORD PTR [edi+2772], eax
	mov eax, DWORD PTR [edi+1368]
	mov DWORD PTR [edi+2776], eax
	mov eax, DWORD PTR [edi+1372]
	mov DWORD PTR [edi+2780], eax
	mov eax, DWORD PTR [edi+1376]
	mov DWORD PTR [edi+2784], eax
	mov eax, DWORD PTR [edi+1380]
	mov DWORD PTR [edi+2788], eax
	mov eax, DWORD PTR [edi+1384]
	mov DWORD PTR [edi+2792], eax
	mov eax, DWORD PTR [edi+1388]
	mov DWORD PTR [edi+2796], eax
	mov eax, DWORD PTR [edi+1392]
	mov DWORD PTR [edi+2800], eax
	mov eax, DWORD PTR [edi+1396]
	mov DWORD PTR [edi+2804], eax
	mov esi, 5120
	mov ebp, edi
	add ebp, esi
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [ebp+44], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [ebp+128], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [ebp+132], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [ebp+136], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [ebp+140], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [ebp+172], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [ebp+264], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [ebp+268], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [ebp+284], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [ebp+288], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [ebp+292], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [ebp+296], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [ebp+300], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [ebp+304], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [ebp+308], eax
	add esi, 384
	cmp esi, 8192
	mov eax, 1600
	mov ecx, 832
	mov edx, 960
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 832
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 960
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 2752
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 2112
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 1600
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 2368
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 960
	mov ecx, 1984
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2752
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
224:
	mov eax, 1600
	mov ecx, 320
	mov edx, 2752
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1600
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 64
	mov edx, 832
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 192
	mov edx, 960
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 1472
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 2112
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 1728
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 1728
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 64
	mov edx, 192
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 832
	mov edx, 960
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 1600
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 1600
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 1984
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 2240
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [edi+372], eax
	mov ebp, edi
	add ebp, esi
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [ebp+44], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [ebp+128], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [ebp+132], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [ebp+136], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [ebp+140], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [ebp+172], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [ebp+264], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [ebp+268], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [ebp+284], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [ebp+288], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [ebp+292], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [ebp+296], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [ebp+300], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [ebp+304], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [ebp+308], eax
	add esi, 384
	cmp esi, 8192
	jne 224b
	mov eax, 64
	mov ecx, 64
	mov edx, 64
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1344]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+1348]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+1352]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+1356]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+1360]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+1364]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+1368]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+1372]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+1376]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+1380]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+1384]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+1388]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+1392]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+1396]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+1344]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+1348]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+1352]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+1356]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+1360]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+1364]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+1368]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+1372]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+1376]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+1380]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+1384]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+1388]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+1392]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+1396]
	mov DWORD PTR [edi+372], eax
	mov esi, 456
225:
	sub esi, 1
	mov eax, 1600
	mov ecx, 64
	mov edx, 192
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 64
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 192
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 320
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 2112
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 1600
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 64
	mov ecx, 2368
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 192
	mov ecx, 1984
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 320
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, edi
	add ebp, esi
	movzx ecx, BYTE PTR [ebp+3072]
	cmp ecx, 0
	jne 226f
	jmp 227f
226:
	sub ecx, 1
	ror ecx, 29
	mov eax, ecx
	ror ecx, 29
	sub ecx, eax
	mov ebp, DWORD PTR [edi+4360]
	add ebp, ecx
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+4]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+8]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+12]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+16]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+20]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+24]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+28]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+32]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+36]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+44]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+48]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+52]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+56]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+60]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+64]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+68]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+72]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+76]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [edi+1268], eax
	mov eax, 1600
	mov ecx, 320
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 64
	mov edx, 1088
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 192
	mov edx, 1216
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 1984
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul_a24}
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 64
	mov edx, 192
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 1088
	mov edx, 1216
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 2112
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 2112
	mov edx, 1728
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 2112
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 1856
	mov edx, 1728
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 1600
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 320
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 64
	mov ecx, 1728
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 320
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 192
	mov ecx, 1728
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 320
	mov ecx, 2368
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
227:
	mov ebp, edi
	add ebp, esi
	movzx ecx, BYTE PTR [ebp+4608]
	cmp ecx, 0
	jne 228f
	jmp 229f
228:
	ror ecx, 26
	mov ebp, ecx
	ror ecx, 31
	add ebp, ecx
	add ebp, edi
	mov eax, DWORD PTR [ebp+4928]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [ebp+4932]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [ebp+4936]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [ebp+4940]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [ebp+4944]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [ebp+4948]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [ebp+4952]
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [ebp+4956]
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [ebp+4960]
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [ebp+4964]
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [ebp+4968]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [ebp+4972]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [ebp+4976]
	mov DWORD PTR [edi+880], eax
	mov eax, DWORD PTR [ebp+4980]
	mov DWORD PTR [edi+884], eax
	mov eax, DWORD PTR [ebp+5056]
	mov DWORD PTR [edi+960], eax
	mov eax, DWORD PTR [ebp+5060]
	mov DWORD PTR [edi+964], eax
	mov eax, DWORD PTR [ebp+5064]
	mov DWORD PTR [edi+968], eax
	mov eax, DWORD PTR [ebp+5068]
	mov DWORD PTR [edi+972], eax
	mov eax, DWORD PTR [ebp+5072]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [ebp+5076]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [ebp+5080]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [ebp+5084]
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [ebp+5088]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [ebp+5092]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [ebp+5096]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [ebp+5100]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [ebp+5104]
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [ebp+5108]
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [ebp+5184]
	mov DWORD PTR [edi+2752], eax
	mov eax, DWORD PTR [ebp+5188]
	mov DWORD PTR [edi+2756], eax
	mov eax, DWORD PTR [ebp+5192]
	mov DWORD PTR [edi+2760], eax
	mov eax, DWORD PTR [ebp+5196]
	mov DWORD PTR [edi+2764], eax
	mov eax, DWORD PTR [ebp+5200]
	mov DWORD PTR [edi+2768], eax
	mov eax, DWORD PTR [ebp+5204]
	mov DWORD PTR [edi+2772], eax
	mov eax, DWORD PTR [ebp+5208]
	mov DWORD PTR [edi+2776], eax
	mov eax, DWORD PTR [ebp+5212]
	mov DWORD PTR [edi+2780], eax
	mov eax, DWORD PTR [ebp+5216]
	mov DWORD PTR [edi+2784], eax
	mov eax, DWORD PTR [ebp+5220]
	mov DWORD PTR [edi+2788], eax
	mov eax, DWORD PTR [ebp+5224]
	mov DWORD PTR [edi+2792], eax
	mov eax, DWORD PTR [ebp+5228]
	mov DWORD PTR [edi+2796], eax
	mov eax, DWORD PTR [ebp+5232]
	mov DWORD PTR [edi+2800], eax
	mov eax, DWORD PTR [ebp+5236]
	mov DWORD PTR [edi+2804], eax
	mov eax, 1600
	mov ecx, 320
	mov edx, 2752
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1600
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 64
	mov edx, 832
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 192
	mov edx, 960
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 1472
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 2112
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 1728
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 1728
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 64
	mov edx, 192
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 832
	mov edx, 960
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 1600
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 1600
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 1984
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 2240
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [edi+372], eax
229:
	cmp esi, 0
	jne 225b
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+880], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+884], eax
	mov eax, DWORD PTR [edi+4096]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+4100]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+4104]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+4108]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+4112]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+4116]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+4120]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+4124]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+4128]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+4132]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+4136]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+4140]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+4144]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+4148]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+4224]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [edi+4228]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [edi+4232]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+4236]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+4240]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+4244]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+4248]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+4252]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [edi+4256]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+4260]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+4264]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+4268]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [edi+4272]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [edi+4276]
	mov DWORD PTR [edi+1268], eax
	mov esi, 2
230:
	mov eax, 1600
	mov ecx, 64
	mov edx, 832
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 64
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 832
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 320
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 2112
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 1600
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 64
	mov ecx, 2368
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 1984
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 320
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1088
	mov edx, 1216
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1088
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1216
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 1344
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 2112
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 1600
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 2368
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1984
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 230b
	mov esi, 2
231:
	mov eax, 1600
	mov ecx, 64
	mov edx, 1344
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1088
	mov edx, 320
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1600]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+1604]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+1608]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+1612]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+1616]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+1620]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+1624]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+1628]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+1632]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+1636]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+1640]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+1644]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+1648]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+1652]
	mov DWORD PTR [edi+244], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+192]
	adc eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	adc eax, 0
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	adc eax, 0
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	adc eax, 0
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	adc eax, 0
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	adc eax, 0
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	adc eax, 0
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	adc eax, 1
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	adc eax, 0
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	adc eax, 0
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	adc eax, 0
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	adc eax, 0
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	adc eax, 0
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	adc eax, 0
	mov DWORD PTR [edi+3892], eax
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+3840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+3844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+3848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+3852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+3856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+3860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+3864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+3868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+3872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+3876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+3880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+3884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+3888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+3892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+1600], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+1604], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+1608], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+1612], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+1616], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+1620], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+1624], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+1628], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+1632], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+1636], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+1640], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+1644], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+1648], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+1652], eax
	mov eax, DWORD PTR [edi+1728]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+1732]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+1736]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+1740]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+1744]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+1748]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+1752]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+244], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+192]
	adc eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	adc eax, 0
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	adc eax, 0
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	adc eax, 0
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	adc eax, 0
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	adc eax, 0
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	adc eax, 0
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	adc eax, 1
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	adc eax, 0
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	adc eax, 0
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	adc eax, 0
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	adc eax, 0
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	adc eax, 0
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	adc eax, 0
	mov DWORD PTR [edi+3892], eax
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+3840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+3844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+3848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+3852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+3856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+3860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+3864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+3868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+3872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+3876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+3880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+3884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+3888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+3892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov ecx, 0
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [edi+1600]
	or ecx, eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [edi+1604]
	or ecx, eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [edi+1608]
	or ecx, eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [edi+1612]
	or ecx, eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [edi+1616]
	or ecx, eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [edi+1620]
	or ecx, eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [edi+1624]
	or ecx, eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [edi+1628]
	or ecx, eax
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [edi+1632]
	or ecx, eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [edi+1636]
	or ecx, eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [edi+1640]
	or ecx, eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [edi+1644]
	or ecx, eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [edi+1648]
	or ecx, eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [edi+1652]
	or ecx, eax
	or ecx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+16], ecx
	mov eax, DWORD PTR [edi+832]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+836]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+856]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+860]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+864]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+868]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+880]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+884]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1140], eax
	sub esi, 1
	jne 231b
	mov ecx, DWORD PTR [edi+16]
	mov eax, 0
	sub eax, ecx
	sbb ecx, ecx
	add ecx, 1
	mov eax, edi
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov ebp, DWORD PTR [eax+12]
	mov edi, DWORD PTR [eax+8]
	mov eax, ecx
	ret
	.p2align 6
