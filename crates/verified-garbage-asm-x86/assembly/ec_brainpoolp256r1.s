// The functions of `src/ec_brainpoolp256r1.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp256r1_public_key:
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_BRAINPOOLP256R1_COMB}
	pop ecx
	mov edx, DWORD PTR [esp+12]
	mov DWORD PTR [edx+60], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1084], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1116], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1148], eax
	mov eax, 527324023
	mov DWORD PTR [edi+64], eax
	mov eax, 538134557
	mov DWORD PTR [edi+68], eax
	mov eax, -718921688
	mov DWORD PTR [edi+72], eax
	mov eax, 1849423395
	mov DWORD PTR [edi+76], eax
	mov eax, -1652322958
	mov DWORD PTR [edi+80], eax
	mov eax, 1046874768
	mov DWORD PTR [edi+84], eax
	mov eax, -1578194500
	mov DWORD PTR [edi+88], eax
	mov eax, -1443145765
	mov DWORD PTR [edi+92], eax
	mov eax, -1756866905
	mov DWORD PTR [edi+96], eax
	mov eax, -1877078398
	mov DWORD PTR [edi+100], eax
	mov eax, -1251891465
	mov DWORD PTR [edi+104], eax
	mov eax, -1942390109
	mov DWORD PTR [edi+108], eax
	mov eax, -1652322959
	mov DWORD PTR [edi+112], eax
	mov eax, 1046874768
	mov DWORD PTR [edi+116], eax
	mov eax, -1578194500
	mov DWORD PTR [edi+120], eax
	mov eax, -1443145765
	mov DWORD PTR [edi+124], eax
	mov eax, 0
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
	mov eax, 0
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
	mov eax, 0
	mov DWORD PTR [edi+208], eax
	mov eax, 0
	mov DWORD PTR [edi+212], eax
	mov eax, 0
	mov DWORD PTR [edi+216], eax
	mov eax, 0
	mov DWORD PTR [edi+220], eax
	mov eax, -527324023
	mov DWORD PTR [edi+224], eax
	mov eax, -538134558
	mov DWORD PTR [edi+228], eax
	mov eax, 718921687
	mov DWORD PTR [edi+232], eax
	mov eax, -1849423396
	mov DWORD PTR [edi+236], eax
	mov eax, 1652322957
	mov DWORD PTR [edi+240], eax
	mov eax, -1046874769
	mov DWORD PTR [edi+244], eax
	mov eax, 1578194499
	mov DWORD PTR [edi+248], eax
	mov eax, 1443145764
	mov DWORD PTR [edi+252], eax
	mov eax, 1768514145
	mov DWORD PTR [edi+256], eax
	mov eax, -707686689
	mov DWORD PTR [edi+260], eax
	mov eax, -1043198876
	mov DWORD PTR [edi+264], eax
	mov eax, -1501486095
	mov DWORD PTR [edi+268], eax
	mov eax, 1670927726
	mov DWORD PTR [edi+272], eax
	mov eax, -1779687842
	mov DWORD PTR [edi+276], eax
	mov eax, -697910249
	mov DWORD PTR [edi+280], eax
	mov eax, 507934379
	mov DWORD PTR [edi+284], eax
	mov eax, 1111677517
	mov DWORD PTR [edi+288], eax
	mov eax, 293005400
	mov DWORD PTR [edi+292], eax
	mov eax, 1693793803
	mov DWORD PTR [edi+296], eax
	mov eax, 541712093
	mov DWORD PTR [edi+300], eax
	mov eax, 131644811
	mov DWORD PTR [edi+304], eax
	mov eax, 778029498
	mov DWORD PTR [edi+308], eax
	mov eax, -739550277
	mov DWORD PTR [edi+312], eax
	mov eax, 1117708386
	mov DWORD PTR [edi+316], eax
	mov eax, 891277580
	mov DWORD PTR [edi+320], eax
	mov eax, 666949933
	mov DWORD PTR [edi+324], eax
	mov eax, -1182993654
	mov DWORD PTR [edi+328], eax
	mov eax, -2132914790
	mov DWORD PTR [edi+332], eax
	mov eax, 1804151507
	mov DWORD PTR [edi+336], eax
	mov eax, 1884041501
	mov DWORD PTR [edi+340], eax
	mov eax, -1643013153
	mov DWORD PTR [edi+344], eax
	mov eax, -1910540678
	mov DWORD PTR [edi+348], eax
	mov eax, -1601078761
	mov DWORD PTR [edi+352], eax
	mov eax, -1706038968
	mov DWORD PTR [edi+356], eax
	mov eax, -845872798
	mov DWORD PTR [edi+360], eax
	mov eax, -1508314535
	mov DWORD PTR [edi+364], eax
	mov eax, -541226237
	mov DWORD PTR [edi+368], eax
	mov eax, 385742568
	mov DWORD PTR [edi+372], eax
	mov eax, 40808610
	mov DWORD PTR [edi+376], eax
	mov eax, 350976198
	mov DWORD PTR [edi+380], eax
	mov eax, 856882342
	mov DWORD PTR [edi+384], eax
	mov eax, -505882402
	mov DWORD PTR [edi+388], eax
	mov eax, 288679072
	mov DWORD PTR [edi+392], eax
	mov eax, -212002966
	mov DWORD PTR [edi+396], eax
	mov eax, 1820417200
	mov DWORD PTR [edi+400], eax
	mov eax, -1686166041
	mov DWORD PTR [edi+404], eax
	mov eax, -1021089950
	mov DWORD PTR [edi+408], eax
	mov eax, 187036089
	mov DWORD PTR [edi+412], eax
	mov eax, 1756866905
	mov DWORD PTR [edi+416], eax
	mov eax, 1877078397
	mov DWORD PTR [edi+420], eax
	mov eax, 1251891464
	mov DWORD PTR [edi+424], eax
	mov eax, 1942390108
	mov DWORD PTR [edi+428], eax
	mov eax, 1652322958
	mov DWORD PTR [edi+432], eax
	mov eax, -1046874769
	mov DWORD PTR [edi+436], eax
	mov eax, 1578194499
	mov DWORD PTR [edi+440], eax
	mov eax, 1443145764
	mov DWORD PTR [edi+444], eax
	mov eax, 527324021
	mov DWORD PTR [edi+448], eax
	mov eax, 538134557
	mov DWORD PTR [edi+452], eax
	mov eax, -718921688
	mov DWORD PTR [edi+456], eax
	mov eax, 1849423395
	mov DWORD PTR [edi+460], eax
	mov eax, -1652322958
	mov DWORD PTR [edi+464], eax
	mov eax, 1046874768
	mov DWORD PTR [edi+468], eax
	mov eax, -1578194500
	mov DWORD PTR [edi+472], eax
	mov eax, -1443145765
	mov DWORD PTR [edi+476], eax
	mov eax, -1756866907
	mov DWORD PTR [edi+480], eax
	mov eax, -1877078398
	mov DWORD PTR [edi+484], eax
	mov eax, -1251891465
	mov DWORD PTR [edi+488], eax
	mov eax, -1942390109
	mov DWORD PTR [edi+492], eax
	mov eax, -1652322959
	mov DWORD PTR [edi+496], eax
	mov eax, 1046874768
	mov DWORD PTR [edi+500], eax
	mov eax, -1578194500
	mov DWORD PTR [edi+504], eax
	mov eax, -1443145765
	mov DWORD PTR [edi+508], eax
	mov eax, 0
	mov DWORD PTR [edi+512], eax
	mov eax, 0
	mov DWORD PTR [edi+516], eax
	mov eax, 0
	mov DWORD PTR [edi+520], eax
	mov eax, 0
	mov DWORD PTR [edi+524], eax
	mov eax, 0
	mov DWORD PTR [edi+528], eax
	mov eax, 0
	mov DWORD PTR [edi+532], eax
	mov eax, 0
	mov DWORD PTR [edi+536], eax
	mov eax, 0
	mov DWORD PTR [edi+540], eax
	mov eax, -527324023
	mov DWORD PTR [edi+544], eax
	mov eax, -538134558
	mov DWORD PTR [edi+548], eax
	mov eax, 718921687
	mov DWORD PTR [edi+552], eax
	mov eax, -1849423396
	mov DWORD PTR [edi+556], eax
	mov eax, 1652322957
	mov DWORD PTR [edi+560], eax
	mov eax, -1046874769
	mov DWORD PTR [edi+564], eax
	mov eax, 1578194499
	mov DWORD PTR [edi+568], eax
	mov eax, 1443145764
	mov DWORD PTR [edi+572], eax
	mov eax, 0
	mov DWORD PTR [edi+576], eax
	mov eax, 0
	mov DWORD PTR [edi+580], eax
	mov eax, 0
	mov DWORD PTR [edi+584], eax
	mov eax, 0
	mov DWORD PTR [edi+588], eax
	mov eax, 0
	mov DWORD PTR [edi+592], eax
	mov eax, 0
	mov DWORD PTR [edi+596], eax
	mov eax, 0
	mov DWORD PTR [edi+600], eax
	mov eax, 0
	mov DWORD PTR [edi+604], eax
	mov eax, -1
	mov DWORD PTR [edi+1472], eax
	mov esi, 32
20:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+1056]
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
	mov esi, 32
21:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+448]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4356], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4357], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4358], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4359], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4360], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4361], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4362], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4363], dl
	test esi, esi
	jne 21b
	mov esi, 32
22:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+480]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4616], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4617], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4618], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4619], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4620], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4621], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4622], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4623], dl
	test esi, esi
	jne 22b
	mov eax, 1111677517
	mov DWORD PTR [edi+1344], eax
	mov eax, 293005400
	mov DWORD PTR [edi+1348], eax
	mov eax, 1693793803
	mov DWORD PTR [edi+1352], eax
	mov eax, 541712093
	mov DWORD PTR [edi+1356], eax
	mov eax, 131644811
	mov DWORD PTR [edi+1360], eax
	mov eax, 778029498
	mov DWORD PTR [edi+1364], eax
	mov eax, -739550277
	mov DWORD PTR [edi+1368], eax
	mov eax, 1117708386
	mov DWORD PTR [edi+1372], eax
	mov eax, -2142001174
	mov DWORD PTR [edi+512], eax
	mov eax, -1786211070
	mov DWORD PTR [edi+516], eax
	mov eax, 150341778
	mov DWORD PTR [edi+520], eax
	mov eax, 1670465039
	mov DWORD PTR [edi+524], eax
	mov eax, 1564422379
	mov DWORD PTR [edi+528], eax
	mov eax, -619988244
	mov DWORD PTR [edi+532], eax
	mov eax, -339845774
	mov DWORD PTR [edi+536], eax
	mov eax, 1038900821
	mov DWORD PTR [edi+540], eax
	mov eax, 1672347678
	mov DWORD PTR [edi+544], eax
	mov eax, -1632594522
	mov DWORD PTR [edi+548], eax
	mov eax, -1496081272
	mov DWORD PTR [edi+552], eax
	mov eax, -404342457
	mov DWORD PTR [edi+556], eax
	mov eax, 927889525
	mov DWORD PTR [edi+560], eax
	mov eax, 1270624715
	mov DWORD PTR [edi+564], eax
	mov eax, 2073490910
	mov DWORD PTR [edi+568], eax
	mov eax, -1777490090
	mov DWORD PTR [edi+572], eax
	mov eax, -527324023
	mov DWORD PTR [edi+576], eax
	mov eax, -538134558
	mov DWORD PTR [edi+580], eax
	mov eax, 718921687
	mov DWORD PTR [edi+584], eax
	mov eax, -1849423396
	mov DWORD PTR [edi+588], eax
	mov eax, 1652322957
	mov DWORD PTR [edi+592], eax
	mov eax, -1046874769
	mov DWORD PTR [edi+596], eax
	mov eax, 1578194499
	mov DWORD PTR [edi+600], eax
	mov eax, 1443145764
	mov DWORD PTR [edi+604], eax
	mov esi, 37
23:
	sub esi, 1
	cmp esi, 36
	je 24f
	mov eax, esi
	mov ecx, 7
	mul ecx
	mov ecx, eax
	add ecx, edi
	mov eax, 0
	add eax, eax
	movzx edx, BYTE PTR [ecx+4102]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4101]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4100]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4099]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4098]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4097]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4096]
	add eax, edx
	sub eax, 64
	mov edx, eax
	shr edx, 31
	mov ebx, 0
	sub ebx, edx
	xor eax, ebx
	sub eax, ebx
	mov ebx, eax
	jmp 25f
24:
	mov eax, esi
	mov ecx, 7
	mul ecx
	mov ecx, eax
	add ecx, edi
	mov eax, 0
	add eax, eax
	movzx edx, BYTE PTR [ecx+4099]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4098]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4097]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4096]
	add eax, edx
	sub eax, 64
	mov edx, eax
	shr edx, 31
	mov ebx, 0
	sub ebx, edx
	xor eax, ebx
	sub eax, ebx
	mov ebx, eax
25:
	mov eax, esi
	mov ecx, 4096
	mul ecx
	mov edx, DWORD PTR [edi+60]
	add edx, eax
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	mov ecx, 1
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+16]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+32]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+48]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 2
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+64]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+80]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+96]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+112]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 3
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+128]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+144]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+160]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+176]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 4
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+192]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+208]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+224]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+240]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 5
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+256]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+272]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+288]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+304]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 6
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+320]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+336]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+352]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+368]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 7
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+384]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+400]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+416]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+432]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 8
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+448]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+464]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+480]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+496]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 9
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+512]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+528]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+544]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+560]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 10
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+576]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+592]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+608]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+624]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 11
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+640]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+656]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+672]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+688]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 12
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+704]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+720]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+736]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+752]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 13
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+768]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+784]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+800]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+816]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 14
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+832]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+848]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+864]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+880]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 15
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+896]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+912]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+928]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+944]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 16
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+960]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+976]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+992]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1008]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 17
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1024]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1040]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1056]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1072]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 18
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1088]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1104]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1120]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1136]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 19
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1152]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1168]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1184]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1200]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 20
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1216]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1232]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1248]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1264]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 21
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1280]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1296]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1312]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1328]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 22
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1344]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1360]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1376]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1392]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 23
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1408]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1424]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1440]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1456]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 24
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1472]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1488]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1504]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1520]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 25
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1536]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1552]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1568]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1584]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 26
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1600]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1616]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1632]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1648]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 27
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1664]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1680]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1696]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1712]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 28
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1728]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1744]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1760]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1776]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 29
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1792]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1808]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1824]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1840]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 30
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1856]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1872]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1888]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1904]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 31
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1920]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1936]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1952]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1968]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 32
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1984]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2000]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2016]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2032]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 33
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2048]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2064]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2080]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2096]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 34
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2112]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2128]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2144]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2160]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 35
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2176]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2192]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2208]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2224]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 36
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2240]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2256]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2272]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2288]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 37
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2304]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2320]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2336]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2352]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 38
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2368]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2384]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2400]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2416]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 39
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2432]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2448]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2464]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2480]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 40
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2496]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2512]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2528]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2544]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 41
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2560]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2576]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2592]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2608]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 42
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2624]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2640]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2656]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2672]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 43
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2688]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2704]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2720]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2736]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 44
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2752]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2768]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2784]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2800]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 45
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2816]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2832]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2848]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2864]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 46
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2880]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2896]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2912]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2928]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 47
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2944]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2960]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2976]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2992]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 48
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3008]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3024]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3040]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3056]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 49
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3072]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3088]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3104]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3120]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 50
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3136]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3152]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3168]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3184]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 51
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3200]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3216]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3232]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3248]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 52
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3264]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3280]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3296]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3312]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 53
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3328]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3344]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3360]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3376]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 54
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3392]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3408]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3424]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3440]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 55
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3456]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3472]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3488]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3504]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 56
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3520]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3536]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3552]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3568]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 57
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3584]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3600]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3616]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3632]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 58
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3648]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3664]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3680]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3696]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 59
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3712]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3728]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3744]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3760]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 60
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3776]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3792]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3808]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3824]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 61
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3840]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3856]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3872]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3888]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 62
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3904]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3920]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3936]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3952]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 63
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3968]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3984]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4000]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4016]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 64
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4032]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4048]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4064]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4080]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu XMMWORD PTR [edi+704], xmm0
	movdqu XMMWORD PTR [edi+720], xmm1
	movdqu XMMWORD PTR [edi+736], xmm2
	movdqu XMMWORD PTR [edi+752], xmm3
	mov eax, -527324023
	mov DWORD PTR [edi+768], eax
	mov eax, -538134558
	mov DWORD PTR [edi+772], eax
	mov eax, 718921687
	mov DWORD PTR [edi+776], eax
	mov eax, -1849423396
	mov DWORD PTR [edi+780], eax
	mov eax, 1652322957
	mov DWORD PTR [edi+784], eax
	mov eax, -1046874769
	mov DWORD PTR [edi+788], eax
	mov eax, 1578194499
	mov DWORD PTR [edi+792], eax
	mov eax, 1443145764
	mov DWORD PTR [edi+796], eax
	mov ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+736]
	mov edx, DWORD PTR [edi+768]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+740]
	mov edx, DWORD PTR [edi+772]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+744]
	mov edx, DWORD PTR [edi+776]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+748]
	mov edx, DWORD PTR [edi+780]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+752]
	mov edx, DWORD PTR [edi+784]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+756]
	mov edx, DWORD PTR [edi+788]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+760]
	mov edx, DWORD PTR [edi+792]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+764]
	mov edx, DWORD PTR [edi+796]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+768]
	mov edx, DWORD PTR [edi+160]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+772]
	mov edx, DWORD PTR [edi+164]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+776]
	mov edx, DWORD PTR [edi+168]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+780]
	mov edx, DWORD PTR [edi+172]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+784]
	mov edx, DWORD PTR [edi+176]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+788]
	mov edx, DWORD PTR [edi+180]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+792]
	mov edx, DWORD PTR [edi+184]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+796]
	mov edx, DWORD PTR [edi+188]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+796], eax
	mov eax, 736
	mov ecx, 160
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	cmp esi, 36
	je 26f
	mov eax, esi
	mov ecx, 7
	mul ecx
	mov ecx, eax
	add ecx, edi
	movzx eax, BYTE PTR [ecx+4102]
	sub eax, 1
	mov ecx, eax
	jmp 27f
26:
	mov ecx, -1
27:
	mov eax, DWORD PTR [edi+736]
	mov edx, DWORD PTR [edi+1024]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+740]
	mov edx, DWORD PTR [edi+1028]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+744]
	mov edx, DWORD PTR [edi+1032]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+748]
	mov edx, DWORD PTR [edi+1036]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+752]
	mov edx, DWORD PTR [edi+1040]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+756]
	mov edx, DWORD PTR [edi+1044]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+760]
	mov edx, DWORD PTR [edi+1048]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+764]
	mov edx, DWORD PTR [edi+1052]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+764], eax
	mov eax, 704
	mov ecx, 512
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 544
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 576
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 512
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 704
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 800
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 512
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 704
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 960
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 800
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 960
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 544
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 736
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 960
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 832
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 960
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 256
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 1344
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 608
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 832
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 832
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 608
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 800
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 832
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 256
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 1344
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 832
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 800
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 256
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 832
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 960
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 896
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 608
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 896
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 960
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 672
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [edi+540], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+604], eax
	test esi, esi
	jne 23b
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+1504], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+1508], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+1512], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+1516], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+1524], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+1532], eax
	mov eax, 0
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+1544], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+1548], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+1552], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+1556], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+1560], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+1564], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+1568], eax
	mov eax, 0
	mov DWORD PTR [edi+1572], eax
	mov eax, 0
	mov DWORD PTR [edi+1576], eax
	mov DWORD PTR [edi+1580], eax
	mov DWORD PTR [edi+1584], eax
	mov DWORD PTR [edi+1588], eax
	mov DWORD PTR [edi+1592], eax
	mov DWORD PTR [edi+1596], eax
	mov DWORD PTR [edi+1600], eax
	mov DWORD PTR [edi+1604], eax
	mov eax, 0
	mov DWORD PTR [edi+1608], eax
	mov DWORD PTR [edi+1612], eax
	mov DWORD PTR [edi+1616], eax
	mov DWORD PTR [edi+1620], eax
	mov DWORD PTR [edi+1624], eax
	mov DWORD PTR [edi+1628], eax
	mov DWORD PTR [edi+1632], eax
	mov DWORD PTR [edi+1636], eax
	mov eax, 1
	mov DWORD PTR [edi+1608], eax
	mov eax, 1
	mov DWORD PTR [edi+1792], eax
	mov eax, 20
	mov DWORD PTR [edi+1820], eax
28:
	mov eax, DWORD PTR [edi+1504]
	mov DWORD PTR [edi+1796], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+1800], eax
	mov eax, 1
	mov DWORD PTR [edi+1804], eax
	mov eax, 0
	mov DWORD PTR [edi+1808], eax
	mov eax, 0
	mov DWORD PTR [edi+1812], eax
	mov eax, 1
	mov DWORD PTR [edi+1816], eax
	mov esi, 30
29:
	sub esi, 1
	mov eax, DWORD PTR [edi+1800]
	mov edx, DWORD PTR [edi+1792]
	mov ebx, edx
	and eax, 1
	mov ecx, 0
	sub ecx, eax
	shr edx, 31
	sub edx, 1
	and edx, ecx
	mov eax, ebx
	xor eax, edx
	sub eax, edx
	add eax, 2
	mov DWORD PTR [edi+1792], eax
	mov ebx, DWORD PTR [edi+1796]
	mov eax, DWORD PTR [edi+1800]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	shr eax, 1
	mov DWORD PTR [edi+1796], ebx
	mov DWORD PTR [edi+1800], eax
	mov ebx, DWORD PTR [edi+1804]
	mov eax, DWORD PTR [edi+1812]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	add ebx, ebx
	mov DWORD PTR [edi+1804], ebx
	mov DWORD PTR [edi+1812], eax
	mov ebx, DWORD PTR [edi+1808]
	mov eax, DWORD PTR [edi+1816]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	add ebx, ebx
	mov DWORD PTR [edi+1808], ebx
	mov DWORD PTR [edi+1816], eax
	test esi, esi
	jne 29b
	mov eax, 0
	mov DWORD PTR [edi+1712], eax
	mov DWORD PTR [edi+1716], eax
	mov DWORD PTR [edi+1720], eax
	mov DWORD PTR [edi+1724], eax
	mov DWORD PTR [edi+1728], eax
	mov DWORD PTR [edi+1732], eax
	mov DWORD PTR [edi+1736], eax
	mov DWORD PTR [edi+1740], eax
	mov DWORD PTR [edi+1744], eax
	mov DWORD PTR [edi+1748], eax
	mov DWORD PTR [edi+1752], eax
	mov ecx, DWORD PTR [edi+1804]
	mov ebp, edi
	mov ebx, 0
	mov eax, DWORD PTR [edi+1504]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1712]
	adc edx, 0
	mov DWORD PTR [ebp+1712], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1508]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1716]
	adc edx, 0
	mov DWORD PTR [ebp+1716], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1512]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1720]
	adc edx, 0
	mov DWORD PTR [ebp+1720], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1516]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1724]
	adc edx, 0
	mov DWORD PTR [ebp+1724], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1520]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1728]
	adc edx, 0
	mov DWORD PTR [ebp+1728], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1524]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1732]
	adc edx, 0
	mov DWORD PTR [ebp+1732], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1528]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1736]
	adc edx, 0
	mov DWORD PTR [ebp+1736], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1532]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1740]
	adc edx, 0
	mov DWORD PTR [ebp+1740], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1536]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1744]
	adc edx, 0
	mov DWORD PTR [ebp+1744], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+1748]
	add eax, ebx
	mov DWORD PTR [ebp+1748], eax
	mov eax, DWORD PTR [ebp+1752]
	adc eax, 0
	mov DWORD PTR [ebp+1752], eax
	mov ecx, DWORD PTR [edi+1808]
	mov ebp, edi
	mov ebx, 0
	mov eax, DWORD PTR [edi+1540]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1712]
	adc edx, 0
	mov DWORD PTR [ebp+1712], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1544]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1716]
	adc edx, 0
	mov DWORD PTR [ebp+1716], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1548]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1720]
	adc edx, 0
	mov DWORD PTR [ebp+1720], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1552]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1724]
	adc edx, 0
	mov DWORD PTR [ebp+1724], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1556]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1728]
	adc edx, 0
	mov DWORD PTR [ebp+1728], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1560]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1732]
	adc edx, 0
	mov DWORD PTR [ebp+1732], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1564]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1736]
	adc edx, 0
	mov DWORD PTR [ebp+1736], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1568]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1740]
	adc edx, 0
	mov DWORD PTR [ebp+1740], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1572]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1744]
	adc edx, 0
	mov DWORD PTR [ebp+1744], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+1748]
	add eax, ebx
	mov DWORD PTR [ebp+1748], eax
	mov eax, DWORD PTR [ebp+1752]
	adc eax, 0
	mov DWORD PTR [ebp+1752], eax
	mov eax, DWORD PTR [edi+1804]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1504]
	and eax, ecx
	mov DWORD PTR [edi+1756], eax
	mov eax, DWORD PTR [edi+1508]
	and eax, ecx
	mov DWORD PTR [edi+1760], eax
	mov eax, DWORD PTR [edi+1512]
	and eax, ecx
	mov DWORD PTR [edi+1764], eax
	mov eax, DWORD PTR [edi+1516]
	and eax, ecx
	mov DWORD PTR [edi+1768], eax
	mov eax, DWORD PTR [edi+1520]
	and eax, ecx
	mov DWORD PTR [edi+1772], eax
	mov eax, DWORD PTR [edi+1524]
	and eax, ecx
	mov DWORD PTR [edi+1776], eax
	mov eax, DWORD PTR [edi+1528]
	and eax, ecx
	mov DWORD PTR [edi+1780], eax
	mov eax, DWORD PTR [edi+1532]
	and eax, ecx
	mov DWORD PTR [edi+1784], eax
	mov eax, DWORD PTR [edi+1716]
	sub eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+1716], eax
	mov eax, DWORD PTR [edi+1720]
	sbb eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+1720], eax
	mov eax, DWORD PTR [edi+1724]
	sbb eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+1724], eax
	mov eax, DWORD PTR [edi+1728]
	sbb eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+1728], eax
	mov eax, DWORD PTR [edi+1732]
	sbb eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+1732], eax
	mov eax, DWORD PTR [edi+1736]
	sbb eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+1736], eax
	mov eax, DWORD PTR [edi+1740]
	sbb eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+1740], eax
	mov eax, DWORD PTR [edi+1744]
	sbb eax, DWORD PTR [edi+1784]
	mov DWORD PTR [edi+1744], eax
	mov eax, DWORD PTR [edi+1808]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1540]
	and eax, ecx
	mov DWORD PTR [edi+1756], eax
	mov eax, DWORD PTR [edi+1544]
	and eax, ecx
	mov DWORD PTR [edi+1760], eax
	mov eax, DWORD PTR [edi+1548]
	and eax, ecx
	mov DWORD PTR [edi+1764], eax
	mov eax, DWORD PTR [edi+1552]
	and eax, ecx
	mov DWORD PTR [edi+1768], eax
	mov eax, DWORD PTR [edi+1556]
	and eax, ecx
	mov DWORD PTR [edi+1772], eax
	mov eax, DWORD PTR [edi+1560]
	and eax, ecx
	mov DWORD PTR [edi+1776], eax
	mov eax, DWORD PTR [edi+1564]
	and eax, ecx
	mov DWORD PTR [edi+1780], eax
	mov eax, DWORD PTR [edi+1568]
	and eax, ecx
	mov DWORD PTR [edi+1784], eax
	mov eax, DWORD PTR [edi+1716]
	sub eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+1716], eax
	mov eax, DWORD PTR [edi+1720]
	sbb eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+1720], eax
	mov eax, DWORD PTR [edi+1724]
	sbb eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+1724], eax
	mov eax, DWORD PTR [edi+1728]
	sbb eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+1728], eax
	mov eax, DWORD PTR [edi+1732]
	sbb eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+1732], eax
	mov eax, DWORD PTR [edi+1736]
	sbb eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+1736], eax
	mov eax, DWORD PTR [edi+1740]
	sbb eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+1740], eax
	mov eax, DWORD PTR [edi+1744]
	sbb eax, DWORD PTR [edi+1784]
	mov DWORD PTR [edi+1744], eax
	mov eax, DWORD PTR [edi+1712]
	mov ebx, DWORD PTR [edi+1716]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1640], eax
	mov eax, DWORD PTR [edi+1716]
	mov ebx, DWORD PTR [edi+1720]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1644], eax
	mov eax, DWORD PTR [edi+1720]
	mov ebx, DWORD PTR [edi+1724]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1648], eax
	mov eax, DWORD PTR [edi+1724]
	mov ebx, DWORD PTR [edi+1728]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1652], eax
	mov eax, DWORD PTR [edi+1728]
	mov ebx, DWORD PTR [edi+1732]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1656], eax
	mov eax, DWORD PTR [edi+1732]
	mov ebx, DWORD PTR [edi+1736]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1660], eax
	mov eax, DWORD PTR [edi+1736]
	mov ebx, DWORD PTR [edi+1740]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1664], eax
	mov eax, DWORD PTR [edi+1740]
	mov ebx, DWORD PTR [edi+1744]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1668], eax
	mov eax, DWORD PTR [edi+1744]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1744]
	mov ebx, ecx
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1672], eax
	mov eax, 0
	mov DWORD PTR [edi+1712], eax
	mov DWORD PTR [edi+1716], eax
	mov DWORD PTR [edi+1720], eax
	mov DWORD PTR [edi+1724], eax
	mov DWORD PTR [edi+1728], eax
	mov DWORD PTR [edi+1732], eax
	mov DWORD PTR [edi+1736], eax
	mov DWORD PTR [edi+1740], eax
	mov DWORD PTR [edi+1744], eax
	mov DWORD PTR [edi+1748], eax
	mov DWORD PTR [edi+1752], eax
	mov ecx, DWORD PTR [edi+1812]
	mov ebp, edi
	mov ebx, 0
	mov eax, DWORD PTR [edi+1504]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1712]
	adc edx, 0
	mov DWORD PTR [ebp+1712], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1508]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1716]
	adc edx, 0
	mov DWORD PTR [ebp+1716], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1512]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1720]
	adc edx, 0
	mov DWORD PTR [ebp+1720], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1516]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1724]
	adc edx, 0
	mov DWORD PTR [ebp+1724], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1520]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1728]
	adc edx, 0
	mov DWORD PTR [ebp+1728], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1524]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1732]
	adc edx, 0
	mov DWORD PTR [ebp+1732], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1528]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1736]
	adc edx, 0
	mov DWORD PTR [ebp+1736], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1532]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1740]
	adc edx, 0
	mov DWORD PTR [ebp+1740], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1536]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1744]
	adc edx, 0
	mov DWORD PTR [ebp+1744], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+1748]
	add eax, ebx
	mov DWORD PTR [ebp+1748], eax
	mov eax, DWORD PTR [ebp+1752]
	adc eax, 0
	mov DWORD PTR [ebp+1752], eax
	mov ecx, DWORD PTR [edi+1816]
	mov ebp, edi
	mov ebx, 0
	mov eax, DWORD PTR [edi+1540]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1712]
	adc edx, 0
	mov DWORD PTR [ebp+1712], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1544]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1716]
	adc edx, 0
	mov DWORD PTR [ebp+1716], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1548]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1720]
	adc edx, 0
	mov DWORD PTR [ebp+1720], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1552]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1724]
	adc edx, 0
	mov DWORD PTR [ebp+1724], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1556]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1728]
	adc edx, 0
	mov DWORD PTR [ebp+1728], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1560]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1732]
	adc edx, 0
	mov DWORD PTR [ebp+1732], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1564]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1736]
	adc edx, 0
	mov DWORD PTR [ebp+1736], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1568]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1740]
	adc edx, 0
	mov DWORD PTR [ebp+1740], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1572]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1744]
	adc edx, 0
	mov DWORD PTR [ebp+1744], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+1748]
	add eax, ebx
	mov DWORD PTR [ebp+1748], eax
	mov eax, DWORD PTR [ebp+1752]
	adc eax, 0
	mov DWORD PTR [ebp+1752], eax
	mov eax, DWORD PTR [edi+1812]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1504]
	and eax, ecx
	mov DWORD PTR [edi+1756], eax
	mov eax, DWORD PTR [edi+1508]
	and eax, ecx
	mov DWORD PTR [edi+1760], eax
	mov eax, DWORD PTR [edi+1512]
	and eax, ecx
	mov DWORD PTR [edi+1764], eax
	mov eax, DWORD PTR [edi+1516]
	and eax, ecx
	mov DWORD PTR [edi+1768], eax
	mov eax, DWORD PTR [edi+1520]
	and eax, ecx
	mov DWORD PTR [edi+1772], eax
	mov eax, DWORD PTR [edi+1524]
	and eax, ecx
	mov DWORD PTR [edi+1776], eax
	mov eax, DWORD PTR [edi+1528]
	and eax, ecx
	mov DWORD PTR [edi+1780], eax
	mov eax, DWORD PTR [edi+1532]
	and eax, ecx
	mov DWORD PTR [edi+1784], eax
	mov eax, DWORD PTR [edi+1716]
	sub eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+1716], eax
	mov eax, DWORD PTR [edi+1720]
	sbb eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+1720], eax
	mov eax, DWORD PTR [edi+1724]
	sbb eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+1724], eax
	mov eax, DWORD PTR [edi+1728]
	sbb eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+1728], eax
	mov eax, DWORD PTR [edi+1732]
	sbb eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+1732], eax
	mov eax, DWORD PTR [edi+1736]
	sbb eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+1736], eax
	mov eax, DWORD PTR [edi+1740]
	sbb eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+1740], eax
	mov eax, DWORD PTR [edi+1744]
	sbb eax, DWORD PTR [edi+1784]
	mov DWORD PTR [edi+1744], eax
	mov eax, DWORD PTR [edi+1816]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1540]
	and eax, ecx
	mov DWORD PTR [edi+1756], eax
	mov eax, DWORD PTR [edi+1544]
	and eax, ecx
	mov DWORD PTR [edi+1760], eax
	mov eax, DWORD PTR [edi+1548]
	and eax, ecx
	mov DWORD PTR [edi+1764], eax
	mov eax, DWORD PTR [edi+1552]
	and eax, ecx
	mov DWORD PTR [edi+1768], eax
	mov eax, DWORD PTR [edi+1556]
	and eax, ecx
	mov DWORD PTR [edi+1772], eax
	mov eax, DWORD PTR [edi+1560]
	and eax, ecx
	mov DWORD PTR [edi+1776], eax
	mov eax, DWORD PTR [edi+1564]
	and eax, ecx
	mov DWORD PTR [edi+1780], eax
	mov eax, DWORD PTR [edi+1568]
	and eax, ecx
	mov DWORD PTR [edi+1784], eax
	mov eax, DWORD PTR [edi+1716]
	sub eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+1716], eax
	mov eax, DWORD PTR [edi+1720]
	sbb eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+1720], eax
	mov eax, DWORD PTR [edi+1724]
	sbb eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+1724], eax
	mov eax, DWORD PTR [edi+1728]
	sbb eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+1728], eax
	mov eax, DWORD PTR [edi+1732]
	sbb eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+1732], eax
	mov eax, DWORD PTR [edi+1736]
	sbb eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+1736], eax
	mov eax, DWORD PTR [edi+1740]
	sbb eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+1740], eax
	mov eax, DWORD PTR [edi+1744]
	sbb eax, DWORD PTR [edi+1784]
	mov DWORD PTR [edi+1744], eax
	mov eax, DWORD PTR [edi+1712]
	mov ebx, DWORD PTR [edi+1716]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1676], eax
	mov eax, DWORD PTR [edi+1716]
	mov ebx, DWORD PTR [edi+1720]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1680], eax
	mov eax, DWORD PTR [edi+1720]
	mov ebx, DWORD PTR [edi+1724]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1684], eax
	mov eax, DWORD PTR [edi+1724]
	mov ebx, DWORD PTR [edi+1728]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1688], eax
	mov eax, DWORD PTR [edi+1728]
	mov ebx, DWORD PTR [edi+1732]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1692], eax
	mov eax, DWORD PTR [edi+1732]
	mov ebx, DWORD PTR [edi+1736]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1696], eax
	mov eax, DWORD PTR [edi+1736]
	mov ebx, DWORD PTR [edi+1740]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1700], eax
	mov eax, DWORD PTR [edi+1740]
	mov ebx, DWORD PTR [edi+1744]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1704], eax
	mov eax, DWORD PTR [edi+1744]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1744]
	mov ebx, ecx
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+1708], eax
	mov eax, DWORD PTR [edi+1640]
	mov DWORD PTR [edi+1504], eax
	mov eax, DWORD PTR [edi+1644]
	mov DWORD PTR [edi+1508], eax
	mov eax, DWORD PTR [edi+1648]
	mov DWORD PTR [edi+1512], eax
	mov eax, DWORD PTR [edi+1652]
	mov DWORD PTR [edi+1516], eax
	mov eax, DWORD PTR [edi+1656]
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [edi+1660]
	mov DWORD PTR [edi+1524], eax
	mov eax, DWORD PTR [edi+1664]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1668]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1672]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1676]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1680]
	mov DWORD PTR [edi+1544], eax
	mov eax, DWORD PTR [edi+1684]
	mov DWORD PTR [edi+1548], eax
	mov eax, DWORD PTR [edi+1688]
	mov DWORD PTR [edi+1552], eax
	mov eax, DWORD PTR [edi+1692]
	mov DWORD PTR [edi+1556], eax
	mov eax, DWORD PTR [edi+1696]
	mov DWORD PTR [edi+1560], eax
	mov eax, DWORD PTR [edi+1700]
	mov DWORD PTR [edi+1564], eax
	mov eax, DWORD PTR [edi+1704]
	mov DWORD PTR [edi+1568], eax
	mov eax, DWORD PTR [edi+1708]
	mov DWORD PTR [edi+1572], eax
	mov eax, 0
	mov DWORD PTR [edi+1712], eax
	mov DWORD PTR [edi+1716], eax
	mov DWORD PTR [edi+1720], eax
	mov DWORD PTR [edi+1724], eax
	mov DWORD PTR [edi+1728], eax
	mov DWORD PTR [edi+1732], eax
	mov DWORD PTR [edi+1736], eax
	mov DWORD PTR [edi+1740], eax
	mov DWORD PTR [edi+1744], eax
	mov DWORD PTR [edi+1748], eax
	mov ecx, DWORD PTR [edi+1804]
	mov ebp, edi
	mov ebx, 0
	mov eax, DWORD PTR [edi+1576]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1712]
	adc edx, 0
	mov DWORD PTR [ebp+1712], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1580]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1716]
	adc edx, 0
	mov DWORD PTR [ebp+1716], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1584]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1720]
	adc edx, 0
	mov DWORD PTR [ebp+1720], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1588]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1724]
	adc edx, 0
	mov DWORD PTR [ebp+1724], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1592]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1728]
	adc edx, 0
	mov DWORD PTR [ebp+1728], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1596]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1732]
	adc edx, 0
	mov DWORD PTR [ebp+1732], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1600]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1736]
	adc edx, 0
	mov DWORD PTR [ebp+1736], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1604]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1740]
	adc edx, 0
	mov DWORD PTR [ebp+1740], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+1744]
	add eax, ebx
	mov DWORD PTR [ebp+1744], eax
	mov eax, DWORD PTR [ebp+1748]
	adc eax, 0
	mov DWORD PTR [ebp+1748], eax
	mov ecx, DWORD PTR [edi+1808]
	mov ebp, edi
	mov ebx, 0
	mov eax, DWORD PTR [edi+1608]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1712]
	adc edx, 0
	mov DWORD PTR [ebp+1712], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1612]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1716]
	adc edx, 0
	mov DWORD PTR [ebp+1716], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1616]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1720]
	adc edx, 0
	mov DWORD PTR [ebp+1720], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1620]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1724]
	adc edx, 0
	mov DWORD PTR [ebp+1724], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1624]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1728]
	adc edx, 0
	mov DWORD PTR [ebp+1728], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1628]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1732]
	adc edx, 0
	mov DWORD PTR [ebp+1732], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1632]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1736]
	adc edx, 0
	mov DWORD PTR [ebp+1736], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1636]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1740]
	adc edx, 0
	mov DWORD PTR [ebp+1740], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+1744]
	add eax, ebx
	mov DWORD PTR [ebp+1744], eax
	mov eax, DWORD PTR [ebp+1748]
	adc eax, 0
	mov DWORD PTR [ebp+1748], eax
	mov eax, DWORD PTR [edi+1804]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1576]
	and eax, ecx
	mov DWORD PTR [edi+1756], eax
	mov eax, DWORD PTR [edi+1580]
	and eax, ecx
	mov DWORD PTR [edi+1760], eax
	mov eax, DWORD PTR [edi+1584]
	and eax, ecx
	mov DWORD PTR [edi+1764], eax
	mov eax, DWORD PTR [edi+1588]
	and eax, ecx
	mov DWORD PTR [edi+1768], eax
	mov eax, DWORD PTR [edi+1592]
	and eax, ecx
	mov DWORD PTR [edi+1772], eax
	mov eax, DWORD PTR [edi+1596]
	and eax, ecx
	mov DWORD PTR [edi+1776], eax
	mov eax, DWORD PTR [edi+1600]
	and eax, ecx
	mov DWORD PTR [edi+1780], eax
	mov eax, DWORD PTR [edi+1604]
	and eax, ecx
	mov DWORD PTR [edi+1784], eax
	mov eax, DWORD PTR [edi+1716]
	sub eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+1716], eax
	mov eax, DWORD PTR [edi+1720]
	sbb eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+1720], eax
	mov eax, DWORD PTR [edi+1724]
	sbb eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+1724], eax
	mov eax, DWORD PTR [edi+1728]
	sbb eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+1728], eax
	mov eax, DWORD PTR [edi+1732]
	sbb eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+1732], eax
	mov eax, DWORD PTR [edi+1736]
	sbb eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+1736], eax
	mov eax, DWORD PTR [edi+1740]
	sbb eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+1740], eax
	mov eax, DWORD PTR [edi+1744]
	sbb eax, DWORD PTR [edi+1784]
	mov DWORD PTR [edi+1744], eax
	mov eax, DWORD PTR [edi+1808]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1608]
	and eax, ecx
	mov DWORD PTR [edi+1756], eax
	mov eax, DWORD PTR [edi+1612]
	and eax, ecx
	mov DWORD PTR [edi+1760], eax
	mov eax, DWORD PTR [edi+1616]
	and eax, ecx
	mov DWORD PTR [edi+1764], eax
	mov eax, DWORD PTR [edi+1620]
	and eax, ecx
	mov DWORD PTR [edi+1768], eax
	mov eax, DWORD PTR [edi+1624]
	and eax, ecx
	mov DWORD PTR [edi+1772], eax
	mov eax, DWORD PTR [edi+1628]
	and eax, ecx
	mov DWORD PTR [edi+1776], eax
	mov eax, DWORD PTR [edi+1632]
	and eax, ecx
	mov DWORD PTR [edi+1780], eax
	mov eax, DWORD PTR [edi+1636]
	and eax, ecx
	mov DWORD PTR [edi+1784], eax
	mov eax, DWORD PTR [edi+1716]
	sub eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+1716], eax
	mov eax, DWORD PTR [edi+1720]
	sbb eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+1720], eax
	mov eax, DWORD PTR [edi+1724]
	sbb eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+1724], eax
	mov eax, DWORD PTR [edi+1728]
	sbb eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+1728], eax
	mov eax, DWORD PTR [edi+1732]
	sbb eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+1732], eax
	mov eax, DWORD PTR [edi+1736]
	sbb eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+1736], eax
	mov eax, DWORD PTR [edi+1740]
	sbb eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+1740], eax
	mov eax, DWORD PTR [edi+1744]
	sbb eax, DWORD PTR [edi+1784]
	mov DWORD PTR [edi+1744], eax
	mov eax, DWORD PTR [edi+1744]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov esi, ecx
	mov eax, 0
	mov DWORD PTR [edi+1748], eax
	mov eax, DWORD PTR [edi+1712]
	mov ecx, -822244935
	mul ecx
	mov DWORD PTR [edi+1756], eax
	mov ecx, DWORD PTR [edi+1756]
	mov ebp, edi
	mov ebx, 0
	mov eax, DWORD PTR [edi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1712]
	adc edx, 0
	mov DWORD PTR [ebp+1712], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1716]
	adc edx, 0
	mov DWORD PTR [ebp+1716], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+72]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1720]
	adc edx, 0
	mov DWORD PTR [ebp+1720], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+76]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1724]
	adc edx, 0
	mov DWORD PTR [ebp+1724], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+80]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1728]
	adc edx, 0
	mov DWORD PTR [ebp+1728], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+84]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1732]
	adc edx, 0
	mov DWORD PTR [ebp+1732], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+88]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1736]
	adc edx, 0
	mov DWORD PTR [ebp+1736], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+92]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1740]
	adc edx, 0
	mov DWORD PTR [ebp+1740], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+1744]
	add eax, ebx
	mov DWORD PTR [ebp+1744], eax
	mov eax, DWORD PTR [ebp+1748]
	adc eax, 0
	mov DWORD PTR [ebp+1748], eax
	mov eax, DWORD PTR [edi+1748]
	add eax, esi
	mov DWORD PTR [edi+1748], eax
	mov eax, DWORD PTR [edi+1748]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+64]
	and eax, ecx
	mov DWORD PTR [edi+1756], eax
	mov eax, DWORD PTR [edi+68]
	and eax, ecx
	mov DWORD PTR [edi+1760], eax
	mov eax, DWORD PTR [edi+72]
	and eax, ecx
	mov DWORD PTR [edi+1764], eax
	mov eax, DWORD PTR [edi+76]
	and eax, ecx
	mov DWORD PTR [edi+1768], eax
	mov eax, DWORD PTR [edi+80]
	and eax, ecx
	mov DWORD PTR [edi+1772], eax
	mov eax, DWORD PTR [edi+84]
	and eax, ecx
	mov DWORD PTR [edi+1776], eax
	mov eax, DWORD PTR [edi+88]
	and eax, ecx
	mov DWORD PTR [edi+1780], eax
	mov eax, DWORD PTR [edi+92]
	and eax, ecx
	mov DWORD PTR [edi+1784], eax
	mov eax, 0
	mov DWORD PTR [edi+1788], eax
	mov eax, DWORD PTR [edi+1716]
	add eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+1716], eax
	mov eax, DWORD PTR [edi+1720]
	adc eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+1720], eax
	mov eax, DWORD PTR [edi+1724]
	adc eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+1724], eax
	mov eax, DWORD PTR [edi+1728]
	adc eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+1728], eax
	mov eax, DWORD PTR [edi+1732]
	adc eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+1732], eax
	mov eax, DWORD PTR [edi+1736]
	adc eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+1736], eax
	mov eax, DWORD PTR [edi+1740]
	adc eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+1740], eax
	mov eax, DWORD PTR [edi+1744]
	adc eax, DWORD PTR [edi+1784]
	mov DWORD PTR [edi+1744], eax
	mov eax, DWORD PTR [edi+1748]
	adc eax, DWORD PTR [edi+1788]
	mov DWORD PTR [edi+1748], eax
	mov eax, DWORD PTR [edi+1716]
	sub eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+1720]
	sbb eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+1724]
	sbb eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+1728]
	sbb eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+1732]
	sbb eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+1736]
	sbb eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+1740]
	sbb eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+1744]
	sbb eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+1748]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ebx, DWORD PTR [edi+1716]
	mov edx, DWORD PTR [edi+128]
	xor edx, ebx
	and edx, eax
	xor ebx, edx
	mov DWORD PTR [edi+1640], ebx
	mov ebx, DWORD PTR [edi+1720]
	mov edx, DWORD PTR [edi+132]
	xor edx, ebx
	and edx, eax
	xor ebx, edx
	mov DWORD PTR [edi+1644], ebx
	mov ebx, DWORD PTR [edi+1724]
	mov edx, DWORD PTR [edi+136]
	xor edx, ebx
	and edx, eax
	xor ebx, edx
	mov DWORD PTR [edi+1648], ebx
	mov ebx, DWORD PTR [edi+1728]
	mov edx, DWORD PTR [edi+140]
	xor edx, ebx
	and edx, eax
	xor ebx, edx
	mov DWORD PTR [edi+1652], ebx
	mov ebx, DWORD PTR [edi+1732]
	mov edx, DWORD PTR [edi+144]
	xor edx, ebx
	and edx, eax
	xor ebx, edx
	mov DWORD PTR [edi+1656], ebx
	mov ebx, DWORD PTR [edi+1736]
	mov edx, DWORD PTR [edi+148]
	xor edx, ebx
	and edx, eax
	xor ebx, edx
	mov DWORD PTR [edi+1660], ebx
	mov ebx, DWORD PTR [edi+1740]
	mov edx, DWORD PTR [edi+152]
	xor edx, ebx
	and edx, eax
	xor ebx, edx
	mov DWORD PTR [edi+1664], ebx
	mov ebx, DWORD PTR [edi+1744]
	mov edx, DWORD PTR [edi+156]
	xor edx, ebx
	and edx, eax
	xor ebx, edx
	mov DWORD PTR [edi+1668], ebx
	mov eax, 0
	mov DWORD PTR [edi+1712], eax
	mov DWORD PTR [edi+1716], eax
	mov DWORD PTR [edi+1720], eax
	mov DWORD PTR [edi+1724], eax
	mov DWORD PTR [edi+1728], eax
	mov DWORD PTR [edi+1732], eax
	mov DWORD PTR [edi+1736], eax
	mov DWORD PTR [edi+1740], eax
	mov DWORD PTR [edi+1744], eax
	mov DWORD PTR [edi+1748], eax
	mov ecx, DWORD PTR [edi+1812]
	mov ebp, edi
	mov ebx, 0
	mov eax, DWORD PTR [edi+1576]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1712]
	adc edx, 0
	mov DWORD PTR [ebp+1712], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1580]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1716]
	adc edx, 0
	mov DWORD PTR [ebp+1716], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1584]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1720]
	adc edx, 0
	mov DWORD PTR [ebp+1720], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1588]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1724]
	adc edx, 0
	mov DWORD PTR [ebp+1724], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1592]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1728]
	adc edx, 0
	mov DWORD PTR [ebp+1728], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1596]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1732]
	adc edx, 0
	mov DWORD PTR [ebp+1732], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1600]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1736]
	adc edx, 0
	mov DWORD PTR [ebp+1736], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1604]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1740]
	adc edx, 0
	mov DWORD PTR [ebp+1740], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+1744]
	add eax, ebx
	mov DWORD PTR [ebp+1744], eax
	mov eax, DWORD PTR [ebp+1748]
	adc eax, 0
	mov DWORD PTR [ebp+1748], eax
	mov ecx, DWORD PTR [edi+1816]
	mov ebp, edi
	mov ebx, 0
	mov eax, DWORD PTR [edi+1608]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1712]
	adc edx, 0
	mov DWORD PTR [ebp+1712], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1612]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1716]
	adc edx, 0
	mov DWORD PTR [ebp+1716], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1616]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1720]
	adc edx, 0
	mov DWORD PTR [ebp+1720], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1620]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1724]
	adc edx, 0
	mov DWORD PTR [ebp+1724], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1624]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1728]
	adc edx, 0
	mov DWORD PTR [ebp+1728], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1628]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1732]
	adc edx, 0
	mov DWORD PTR [ebp+1732], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1632]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1736]
	adc edx, 0
	mov DWORD PTR [ebp+1736], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+1636]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1740]
	adc edx, 0
	mov DWORD PTR [ebp+1740], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+1744]
	add eax, ebx
	mov DWORD PTR [ebp+1744], eax
	mov eax, DWORD PTR [ebp+1748]
	adc eax, 0
	mov DWORD PTR [ebp+1748], eax
	mov eax, DWORD PTR [edi+1812]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1576]
	and eax, ecx
	mov DWORD PTR [edi+1756], eax
	mov eax, DWORD PTR [edi+1580]
	and eax, ecx
	mov DWORD PTR [edi+1760], eax
	mov eax, DWORD PTR [edi+1584]
	and eax, ecx
	mov DWORD PTR [edi+1764], eax
	mov eax, DWORD PTR [edi+1588]
	and eax, ecx
	mov DWORD PTR [edi+1768], eax
	mov eax, DWORD PTR [edi+1592]
	and eax, ecx
	mov DWORD PTR [edi+1772], eax
	mov eax, DWORD PTR [edi+1596]
	and eax, ecx
	mov DWORD PTR [edi+1776], eax
	mov eax, DWORD PTR [edi+1600]
	and eax, ecx
	mov DWORD PTR [edi+1780], eax
	mov eax, DWORD PTR [edi+1604]
	and eax, ecx
	mov DWORD PTR [edi+1784], eax
	mov eax, DWORD PTR [edi+1716]
	sub eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+1716], eax
	mov eax, DWORD PTR [edi+1720]
	sbb eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+1720], eax
	mov eax, DWORD PTR [edi+1724]
	sbb eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+1724], eax
	mov eax, DWORD PTR [edi+1728]
	sbb eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+1728], eax
	mov eax, DWORD PTR [edi+1732]
	sbb eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+1732], eax
	mov eax, DWORD PTR [edi+1736]
	sbb eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+1736], eax
	mov eax, DWORD PTR [edi+1740]
	sbb eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+1740], eax
	mov eax, DWORD PTR [edi+1744]
	sbb eax, DWORD PTR [edi+1784]
	mov DWORD PTR [edi+1744], eax
	mov eax, DWORD PTR [edi+1816]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1608]
	and eax, ecx
	mov DWORD PTR [edi+1756], eax
	mov eax, DWORD PTR [edi+1612]
	and eax, ecx
	mov DWORD PTR [edi+1760], eax
	mov eax, DWORD PTR [edi+1616]
	and eax, ecx
	mov DWORD PTR [edi+1764], eax
	mov eax, DWORD PTR [edi+1620]
	and eax, ecx
	mov DWORD PTR [edi+1768], eax
	mov eax, DWORD PTR [edi+1624]
	and eax, ecx
	mov DWORD PTR [edi+1772], eax
	mov eax, DWORD PTR [edi+1628]
	and eax, ecx
	mov DWORD PTR [edi+1776], eax
	mov eax, DWORD PTR [edi+1632]
	and eax, ecx
	mov DWORD PTR [edi+1780], eax
	mov eax, DWORD PTR [edi+1636]
	and eax, ecx
	mov DWORD PTR [edi+1784], eax
	mov eax, DWORD PTR [edi+1716]
	sub eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+1716], eax
	mov eax, DWORD PTR [edi+1720]
	sbb eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+1720], eax
	mov eax, DWORD PTR [edi+1724]
	sbb eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+1724], eax
	mov eax, DWORD PTR [edi+1728]
	sbb eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+1728], eax
	mov eax, DWORD PTR [edi+1732]
	sbb eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+1732], eax
	mov eax, DWORD PTR [edi+1736]
	sbb eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+1736], eax
	mov eax, DWORD PTR [edi+1740]
	sbb eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+1740], eax
	mov eax, DWORD PTR [edi+1744]
	sbb eax, DWORD PTR [edi+1784]
	mov DWORD PTR [edi+1744], eax
	mov eax, DWORD PTR [edi+1744]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov esi, ecx
	mov eax, 0
	mov DWORD PTR [edi+1748], eax
	mov eax, DWORD PTR [edi+1712]
	mov ecx, -822244935
	mul ecx
	mov DWORD PTR [edi+1756], eax
	mov ecx, DWORD PTR [edi+1756]
	mov ebp, edi
	mov ebx, 0
	mov eax, DWORD PTR [edi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1712]
	adc edx, 0
	mov DWORD PTR [ebp+1712], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1716]
	adc edx, 0
	mov DWORD PTR [ebp+1716], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+72]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1720]
	adc edx, 0
	mov DWORD PTR [ebp+1720], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+76]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1724]
	adc edx, 0
	mov DWORD PTR [ebp+1724], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+80]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1728]
	adc edx, 0
	mov DWORD PTR [ebp+1728], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+84]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1732]
	adc edx, 0
	mov DWORD PTR [ebp+1732], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+88]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1736]
	adc edx, 0
	mov DWORD PTR [ebp+1736], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+92]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1740]
	adc edx, 0
	mov DWORD PTR [ebp+1740], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+1744]
	add eax, ebx
	mov DWORD PTR [ebp+1744], eax
	mov eax, DWORD PTR [ebp+1748]
	adc eax, 0
	mov DWORD PTR [ebp+1748], eax
	mov eax, DWORD PTR [edi+1748]
	add eax, esi
	mov DWORD PTR [edi+1748], eax
	mov eax, DWORD PTR [edi+1748]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+64]
	and eax, ecx
	mov DWORD PTR [edi+1756], eax
	mov eax, DWORD PTR [edi+68]
	and eax, ecx
	mov DWORD PTR [edi+1760], eax
	mov eax, DWORD PTR [edi+72]
	and eax, ecx
	mov DWORD PTR [edi+1764], eax
	mov eax, DWORD PTR [edi+76]
	and eax, ecx
	mov DWORD PTR [edi+1768], eax
	mov eax, DWORD PTR [edi+80]
	and eax, ecx
	mov DWORD PTR [edi+1772], eax
	mov eax, DWORD PTR [edi+84]
	and eax, ecx
	mov DWORD PTR [edi+1776], eax
	mov eax, DWORD PTR [edi+88]
	and eax, ecx
	mov DWORD PTR [edi+1780], eax
	mov eax, DWORD PTR [edi+92]
	and eax, ecx
	mov DWORD PTR [edi+1784], eax
	mov eax, 0
	mov DWORD PTR [edi+1788], eax
	mov eax, DWORD PTR [edi+1716]
	add eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+1716], eax
	mov eax, DWORD PTR [edi+1720]
	adc eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+1720], eax
	mov eax, DWORD PTR [edi+1724]
	adc eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+1724], eax
	mov eax, DWORD PTR [edi+1728]
	adc eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+1728], eax
	mov eax, DWORD PTR [edi+1732]
	adc eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+1732], eax
	mov eax, DWORD PTR [edi+1736]
	adc eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+1736], eax
	mov eax, DWORD PTR [edi+1740]
	adc eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+1740], eax
	mov eax, DWORD PTR [edi+1744]
	adc eax, DWORD PTR [edi+1784]
	mov DWORD PTR [edi+1744], eax
	mov eax, DWORD PTR [edi+1748]
	adc eax, DWORD PTR [edi+1788]
	mov DWORD PTR [edi+1748], eax
	mov eax, DWORD PTR [edi+1716]
	sub eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+1720]
	sbb eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+1724]
	sbb eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+1728]
	sbb eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+1732]
	sbb eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+1736]
	sbb eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+1740]
	sbb eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+1744]
	sbb eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+1748]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ebx, DWORD PTR [edi+1716]
	mov edx, DWORD PTR [edi+128]
	xor edx, ebx
	and edx, eax
	xor ebx, edx
	mov DWORD PTR [edi+1608], ebx
	mov ebx, DWORD PTR [edi+1720]
	mov edx, DWORD PTR [edi+132]
	xor edx, ebx
	and edx, eax
	xor ebx, edx
	mov DWORD PTR [edi+1612], ebx
	mov ebx, DWORD PTR [edi+1724]
	mov edx, DWORD PTR [edi+136]
	xor edx, ebx
	and edx, eax
	xor ebx, edx
	mov DWORD PTR [edi+1616], ebx
	mov ebx, DWORD PTR [edi+1728]
	mov edx, DWORD PTR [edi+140]
	xor edx, ebx
	and edx, eax
	xor ebx, edx
	mov DWORD PTR [edi+1620], ebx
	mov ebx, DWORD PTR [edi+1732]
	mov edx, DWORD PTR [edi+144]
	xor edx, ebx
	and edx, eax
	xor ebx, edx
	mov DWORD PTR [edi+1624], ebx
	mov ebx, DWORD PTR [edi+1736]
	mov edx, DWORD PTR [edi+148]
	xor edx, ebx
	and edx, eax
	xor ebx, edx
	mov DWORD PTR [edi+1628], ebx
	mov ebx, DWORD PTR [edi+1740]
	mov edx, DWORD PTR [edi+152]
	xor edx, ebx
	and edx, eax
	xor ebx, edx
	mov DWORD PTR [edi+1632], ebx
	mov ebx, DWORD PTR [edi+1744]
	mov edx, DWORD PTR [edi+156]
	xor edx, ebx
	and edx, eax
	xor ebx, edx
	mov DWORD PTR [edi+1636], ebx
	mov eax, DWORD PTR [edi+1640]
	mov DWORD PTR [edi+1576], eax
	mov eax, DWORD PTR [edi+1644]
	mov DWORD PTR [edi+1580], eax
	mov eax, DWORD PTR [edi+1648]
	mov DWORD PTR [edi+1584], eax
	mov eax, DWORD PTR [edi+1652]
	mov DWORD PTR [edi+1588], eax
	mov eax, DWORD PTR [edi+1656]
	mov DWORD PTR [edi+1592], eax
	mov eax, DWORD PTR [edi+1660]
	mov DWORD PTR [edi+1596], eax
	mov eax, DWORD PTR [edi+1664]
	mov DWORD PTR [edi+1600], eax
	mov eax, DWORD PTR [edi+1668]
	mov DWORD PTR [edi+1604], eax
	mov esi, DWORD PTR [edi+1820]
	sub esi, 1
	mov DWORD PTR [edi+1820], esi
	test esi, esi
	jne 28b
	mov eax, -143891673
	mov DWORD PTR [edi+1640], eax
	mov eax, -1795210147
	mov DWORD PTR [edi+1644], eax
	mov eax, 959843720
	mov DWORD PTR [edi+1648], eax
	mov eax, -1632119320
	mov DWORD PTR [edi+1652], eax
	mov eax, 1434779515
	mov DWORD PTR [edi+1656], eax
	mov eax, -1257620988
	mov DWORD PTR [edi+1660], eax
	mov eax, -1804634945
	mov DWORD PTR [edi+1664], eax
	mov eax, -2134865331
	mov DWORD PTR [edi+1668], eax
	mov eax, 671215696
	mov DWORD PTR [edi+1676], eax
	mov eax, -1961622593
	mov DWORD PTR [edi+1680], eax
	mov eax, -1678765409
	mov DWORD PTR [edi+1684], eax
	mov eax, -813424581
	mov DWORD PTR [edi+1688], eax
	mov eax, 1207864822
	mov DWORD PTR [edi+1692], eax
	mov eax, -1990471540
	mov DWORD PTR [edi+1696], eax
	mov eax, 226440444
	mov DWORD PTR [edi+1700], eax
	mov eax, 691719566
	mov DWORD PTR [edi+1704], eax
	mov eax, DWORD PTR [edi+1504]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1640]
	mov edx, DWORD PTR [edi+1676]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1640], eax
	mov eax, DWORD PTR [edi+1644]
	mov edx, DWORD PTR [edi+1680]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1644], eax
	mov eax, DWORD PTR [edi+1648]
	mov edx, DWORD PTR [edi+1684]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1648], eax
	mov eax, DWORD PTR [edi+1652]
	mov edx, DWORD PTR [edi+1688]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1652], eax
	mov eax, DWORD PTR [edi+1656]
	mov edx, DWORD PTR [edi+1692]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1656], eax
	mov eax, DWORD PTR [edi+1660]
	mov edx, DWORD PTR [edi+1696]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1660], eax
	mov eax, DWORD PTR [edi+1664]
	mov edx, DWORD PTR [edi+1700]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1664], eax
	mov eax, DWORD PTR [edi+1668]
	mov edx, DWORD PTR [edi+1704]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1668], eax
	mov eax, 1640
	mov ecx, 1576
	mov edx, 992
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 992
	mov ecx, 512
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 192
	mov ecx, 1152
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 992
	mov ecx, 544
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 192
	mov ecx, 1280
	mov edx, 1440
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1088]
	sub edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+1092]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+1096]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+1100]
	sbb edx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+1104]
	sbb edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+1108]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+1112]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+1116]
	sbb edx, DWORD PTR [edi+124]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+1088]
	or edx, DWORD PTR [edi+1092]
	or edx, DWORD PTR [edi+1096]
	or edx, DWORD PTR [edi+1100]
	or edx, DWORD PTR [edi+1104]
	or edx, DWORD PTR [edi+1108]
	or edx, DWORD PTR [edi+1112]
	or edx, DWORD PTR [edi+1116]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov edx, DWORD PTR [edi+576]
	or edx, DWORD PTR [edi+580]
	or edx, DWORD PTR [edi+584]
	or edx, DWORD PTR [edi+588]
	or edx, DWORD PTR [edi+592]
	or edx, DWORD PTR [edi+596]
	or edx, DWORD PTR [edi+600]
	or edx, DWORD PTR [edi+604]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov ecx, DWORD PTR [edi+1472]
	mov ebx, DWORD PTR [esp+4]
	mov eax, 4
	and eax, ecx
	mov BYTE PTR [ebx], al
	mov eax, DWORD PTR [edi+1184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+29], eax
	mov eax, DWORD PTR [edi+1188]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+25], eax
	mov eax, DWORD PTR [edi+1192]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+21], eax
	mov eax, DWORD PTR [edi+1196]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+17], eax
	mov eax, DWORD PTR [edi+1200]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+13], eax
	mov eax, DWORD PTR [edi+1204]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+9], eax
	mov eax, DWORD PTR [edi+1208]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+5], eax
	mov eax, DWORD PTR [edi+1212]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+1], eax
	mov eax, DWORD PTR [edi+1440]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+61], eax
	mov eax, DWORD PTR [edi+1444]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+57], eax
	mov eax, DWORD PTR [edi+1448]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+53], eax
	mov eax, DWORD PTR [edi+1452]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+49], eax
	mov eax, DWORD PTR [edi+1456]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+45], eax
	mov eax, DWORD PTR [edi+1460]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+41], eax
	mov eax, DWORD PTR [edi+1464]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+37], eax
	mov eax, DWORD PTR [edi+1468]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+33], eax
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	ret
	.p2align 6
