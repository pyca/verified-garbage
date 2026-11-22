// The functions of `src/ecdsa_brainpoolp256r1.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp256r1_verify:
	lea esp, [esp-108]
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+12]
	cmp eax, 32
	jb 20f
	mov ecx, DWORD PTR [esp+8]
	movzx eax, BYTE PTR [ecx]
	mov BYTE PTR [esp+28], al
	movzx eax, BYTE PTR [ecx+1]
	mov BYTE PTR [esp+29], al
	movzx eax, BYTE PTR [ecx+2]
	mov BYTE PTR [esp+30], al
	movzx eax, BYTE PTR [ecx+3]
	mov BYTE PTR [esp+31], al
	movzx eax, BYTE PTR [ecx+4]
	mov BYTE PTR [esp+32], al
	movzx eax, BYTE PTR [ecx+5]
	mov BYTE PTR [esp+33], al
	movzx eax, BYTE PTR [ecx+6]
	mov BYTE PTR [esp+34], al
	movzx eax, BYTE PTR [ecx+7]
	mov BYTE PTR [esp+35], al
	movzx eax, BYTE PTR [ecx+8]
	mov BYTE PTR [esp+36], al
	movzx eax, BYTE PTR [ecx+9]
	mov BYTE PTR [esp+37], al
	movzx eax, BYTE PTR [ecx+10]
	mov BYTE PTR [esp+38], al
	movzx eax, BYTE PTR [ecx+11]
	mov BYTE PTR [esp+39], al
	movzx eax, BYTE PTR [ecx+12]
	mov BYTE PTR [esp+40], al
	movzx eax, BYTE PTR [ecx+13]
	mov BYTE PTR [esp+41], al
	movzx eax, BYTE PTR [ecx+14]
	mov BYTE PTR [esp+42], al
	movzx eax, BYTE PTR [ecx+15]
	mov BYTE PTR [esp+43], al
	movzx eax, BYTE PTR [ecx+16]
	mov BYTE PTR [esp+44], al
	movzx eax, BYTE PTR [ecx+17]
	mov BYTE PTR [esp+45], al
	movzx eax, BYTE PTR [ecx+18]
	mov BYTE PTR [esp+46], al
	movzx eax, BYTE PTR [ecx+19]
	mov BYTE PTR [esp+47], al
	movzx eax, BYTE PTR [ecx+20]
	mov BYTE PTR [esp+48], al
	movzx eax, BYTE PTR [ecx+21]
	mov BYTE PTR [esp+49], al
	movzx eax, BYTE PTR [ecx+22]
	mov BYTE PTR [esp+50], al
	movzx eax, BYTE PTR [ecx+23]
	mov BYTE PTR [esp+51], al
	movzx eax, BYTE PTR [ecx+24]
	mov BYTE PTR [esp+52], al
	movzx eax, BYTE PTR [ecx+25]
	mov BYTE PTR [esp+53], al
	movzx eax, BYTE PTR [ecx+26]
	mov BYTE PTR [esp+54], al
	movzx eax, BYTE PTR [ecx+27]
	mov BYTE PTR [esp+55], al
	movzx eax, BYTE PTR [ecx+28]
	mov BYTE PTR [esp+56], al
	movzx eax, BYTE PTR [ecx+29]
	mov BYTE PTR [esp+57], al
	movzx eax, BYTE PTR [ecx+30]
	mov BYTE PTR [esp+58], al
	movzx eax, BYTE PTR [ecx+31]
	mov BYTE PTR [esp+59], al
	jmp 21f
20:
	mov eax, 0
	mov DWORD PTR [esp+28], eax
	mov DWORD PTR [esp+32], eax
	mov DWORD PTR [esp+36], eax
	mov DWORD PTR [esp+40], eax
	mov DWORD PTR [esp+44], eax
	mov DWORD PTR [esp+48], eax
	mov DWORD PTR [esp+52], eax
	mov DWORD PTR [esp+56], eax
	mov DWORD PTR [esp+60], eax
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+96], eax
	mov ecx, DWORD PTR [esp+8]
	mov edx, esp
	add edx, 60
	mov eax, DWORD PTR [esp+12]
	sub edx, eax
	test eax, eax
	je 22f
24:
	movzx eax, BYTE PTR [ecx]
	mov BYTE PTR [edx], al
	add ecx, 1
	add edx, 1
	mov eax, edx
	sub eax, esp
	cmp eax, 60
	jne 24b
	jmp 23f
22:
23:
21:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [esp+16], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_BRAINPOOLP256R1_COMB}
	pop ecx
	mov edx, DWORD PTR [esp+16]
	mov DWORD PTR [edx+60], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+12]
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
25:
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
	jne 25b
	mov esi, 32
26:
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
	jne 26b
	mov esi, 32
27:
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
	jne 27b
	mov ebx, DWORD PTR [esp+12]
	add ebx, 32
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1052], eax
	mov eax, -1505338516
	mov DWORD PTR [edi+1312], eax
	mov eax, -1929453701
	mov DWORD PTR [edi+1316], eax
	mov eax, 1632456525
	mov DWORD PTR [edi+1320], eax
	mov eax, 1557023782
	mov DWORD PTR [edi+1324], eax
	mov eax, 1796917255
	mov DWORD PTR [edi+1328], eax
	mov eax, -1578313011
	mov DWORD PTR [edi+1332], eax
	mov eax, -443187288
	mov DWORD PTR [edi+1336], eax
	mov eax, 1192733217
	mov DWORD PTR [edi+1340], eax
	mov eax, -1061096593
	mov DWORD PTR [edi+1344], eax
	mov eax, 97668466
	mov DWORD PTR [edi+1348], eax
	mov eax, -867057831
	mov DWORD PTR [edi+1352], eax
	mov eax, 180570697
	mov DWORD PTR [edi+1356], eax
	mov eax, 1475537369
	mov DWORD PTR [edi+1360], eax
	mov eax, 1690998931
	mov DWORD PTR [edi+1364], eax
	mov eax, 1185139006
	mov DWORD PTR [edi+1368], eax
	mov eax, 372569462
	mov DWORD PTR [edi+1372], eax
	mov ebx, DWORD PTR [esp+4]
	add ebx, 1
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
	add ebx, 32
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1244], eax
	mov ebx, DWORD PTR [esp+4]
	movzx edx, BYTE PTR [ebx]
	xor edx, 4
	sub edx, 1
	sbb edx, edx
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov edx, DWORD PTR [edi+1120]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+1124]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+1128]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+1132]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+1136]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+1140]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+1144]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+1148]
	sbb edx, DWORD PTR [edi+92]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov edx, DWORD PTR [edi+1216]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+1220]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+1224]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+1228]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+1232]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+1236]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+1240]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+1244]
	sbb edx, DWORD PTR [edi+92]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov eax, 1312
	mov ecx, 1120
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
	mov eax, 1312
	mov ecx, 1216
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
	mov eax, 1184
	mov ecx, 1184
	mov edx, 1248
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1152
	mov edx, 1376
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1376
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 256
	mov edx, 1376
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1376
	mov ecx, 1408
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1280
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1248
	mov edx, 1376
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1376]
	or edx, DWORD PTR [edi+1380]
	or edx, DWORD PTR [edi+1384]
	or edx, DWORD PTR [edi+1388]
	or edx, DWORD PTR [edi+1392]
	or edx, DWORD PTR [edi+1396]
	or edx, DWORD PTR [edi+1400]
	or edx, DWORD PTR [edi+1404]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov ecx, DWORD PTR [edi+1472]
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+1152]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1280], eax
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+1156]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1284], eax
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+1160]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1288], eax
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+1164]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1292], eax
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+1168]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1296], eax
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+1172]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1300], eax
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+1176]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1304], eax
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+1180]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1308], eax
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+1184]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1440], eax
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+1188]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1444], eax
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+1192]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1448], eax
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+1196]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1452], eax
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+1200]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+1204]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+1208]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+1212]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1468], eax
	mov edx, DWORD PTR [edi+1056]
	sub edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+1060]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+1064]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+1068]
	sbb edx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+1072]
	sbb edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+1076]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+1080]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+1084]
	sbb edx, DWORD PTR [edi+124]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+1056]
	or edx, DWORD PTR [edi+1060]
	or edx, DWORD PTR [edi+1064]
	or edx, DWORD PTR [edi+1068]
	or edx, DWORD PTR [edi+1072]
	or edx, DWORD PTR [edi+1076]
	or edx, DWORD PTR [edi+1080]
	or edx, DWORD PTR [edi+1084]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov edx, DWORD PTR [edi+1024]
	sub edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+1028]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+1032]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+1036]
	sbb edx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+1040]
	sbb edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+1044]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+1048]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+1052]
	sbb edx, DWORD PTR [edi+124]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+1024]
	or edx, DWORD PTR [edi+1028]
	or edx, DWORD PTR [edi+1032]
	or edx, DWORD PTR [edi+1036]
	or edx, DWORD PTR [edi+1040]
	or edx, DWORD PTR [edi+1044]
	or edx, DWORD PTR [edi+1048]
	or edx, DWORD PTR [edi+1052]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov eax, 384
	mov ecx, 1024
	mov edx, 1248
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+1504], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+1508], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+1512], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+1516], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+1524], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+1532], eax
	mov eax, 0
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1544], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1548], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1552], eax
	mov eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1556], eax
	mov eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1560], eax
	mov eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1564], eax
	mov eax, DWORD PTR [edi+1276]
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
	mov ecx, -877392151
	mul ecx
	mov DWORD PTR [edi+1756], eax
	mov ecx, DWORD PTR [edi+1756]
	mov ebp, edi
	mov ebx, 0
	mov eax, DWORD PTR [edi+96]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1712]
	adc edx, 0
	mov DWORD PTR [ebp+1712], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+100]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1716]
	adc edx, 0
	mov DWORD PTR [ebp+1716], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+104]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1720]
	adc edx, 0
	mov DWORD PTR [ebp+1720], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+108]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1724]
	adc edx, 0
	mov DWORD PTR [ebp+1724], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+112]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1728]
	adc edx, 0
	mov DWORD PTR [ebp+1728], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+116]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1732]
	adc edx, 0
	mov DWORD PTR [ebp+1732], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+120]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1736]
	adc edx, 0
	mov DWORD PTR [ebp+1736], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+124]
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
	mov eax, DWORD PTR [edi+96]
	and eax, ecx
	mov DWORD PTR [edi+1756], eax
	mov eax, DWORD PTR [edi+100]
	and eax, ecx
	mov DWORD PTR [edi+1760], eax
	mov eax, DWORD PTR [edi+104]
	and eax, ecx
	mov DWORD PTR [edi+1764], eax
	mov eax, DWORD PTR [edi+108]
	and eax, ecx
	mov DWORD PTR [edi+1768], eax
	mov eax, DWORD PTR [edi+112]
	and eax, ecx
	mov DWORD PTR [edi+1772], eax
	mov eax, DWORD PTR [edi+116]
	and eax, ecx
	mov DWORD PTR [edi+1776], eax
	mov eax, DWORD PTR [edi+120]
	and eax, ecx
	mov DWORD PTR [edi+1780], eax
	mov eax, DWORD PTR [edi+124]
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
	sub eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+1720]
	sbb eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+1724]
	sbb eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+1728]
	sbb eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+1732]
	sbb eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+1736]
	sbb eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+1740]
	sbb eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+1744]
	sbb eax, DWORD PTR [edi+124]
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
	mov ecx, -877392151
	mul ecx
	mov DWORD PTR [edi+1756], eax
	mov ecx, DWORD PTR [edi+1756]
	mov ebp, edi
	mov ebx, 0
	mov eax, DWORD PTR [edi+96]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1712]
	adc edx, 0
	mov DWORD PTR [ebp+1712], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+100]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1716]
	adc edx, 0
	mov DWORD PTR [ebp+1716], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+104]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1720]
	adc edx, 0
	mov DWORD PTR [ebp+1720], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+108]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1724]
	adc edx, 0
	mov DWORD PTR [ebp+1724], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+112]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1728]
	adc edx, 0
	mov DWORD PTR [ebp+1728], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+116]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1732]
	adc edx, 0
	mov DWORD PTR [ebp+1732], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+120]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+1736]
	adc edx, 0
	mov DWORD PTR [ebp+1736], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+124]
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
	mov eax, DWORD PTR [edi+96]
	and eax, ecx
	mov DWORD PTR [edi+1756], eax
	mov eax, DWORD PTR [edi+100]
	and eax, ecx
	mov DWORD PTR [edi+1760], eax
	mov eax, DWORD PTR [edi+104]
	and eax, ecx
	mov DWORD PTR [edi+1764], eax
	mov eax, DWORD PTR [edi+108]
	and eax, ecx
	mov DWORD PTR [edi+1768], eax
	mov eax, DWORD PTR [edi+112]
	and eax, ecx
	mov DWORD PTR [edi+1772], eax
	mov eax, DWORD PTR [edi+116]
	and eax, ecx
	mov DWORD PTR [edi+1776], eax
	mov eax, DWORD PTR [edi+120]
	and eax, ecx
	mov DWORD PTR [edi+1780], eax
	mov eax, DWORD PTR [edi+124]
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
	sub eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+1720]
	sbb eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+1724]
	sbb eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+1728]
	sbb eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+1732]
	sbb eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+1736]
	sbb eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+1740]
	sbb eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+1744]
	sbb eax, DWORD PTR [edi+124]
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
	mov eax, -545608076
	mov DWORD PTR [edi+1640], eax
	mov eax, 1443593074
	mov DWORD PTR [edi+1644], eax
	mov eax, 1942766782
	mov DWORD PTR [edi+1648], eax
	mov eax, -245870502
	mov DWORD PTR [edi+1652], eax
	mov eax, -1105617045
	mov DWORD PTR [edi+1656], eax
	mov eax, -361589482
	mov DWORD PTR [edi+1660], eax
	mov eax, 588245468
	mov DWORD PTR [edi+1664], eax
	mov eax, 902285683
	mov DWORD PTR [edi+1668], eax
	mov eax, -1211258829
	mov DWORD PTR [edi+1676], eax
	mov eax, 974295823
	mov DWORD PTR [edi+1680], eax
	mov eax, 1100309049
	mov DWORD PTR [edi+1684], eax
	mov eax, -1696519607
	mov DWORD PTR [edi+1688], eax
	mov eax, -546705915
	mov DWORD PTR [edi+1692], eax
	mov eax, 1408464249
	mov DWORD PTR [edi+1696], eax
	mov eax, 2128527327
	mov DWORD PTR [edi+1700], eax
	mov eax, 1949535848
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
	call {vg_brainpoolp256r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 384
	mov ecx, 1088
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 384
	mov ecx, 1056
	mov edx, 1312
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 992
	mov ecx, 1344
	mov edx, 1376
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 992
	mov ecx, 1312
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 192
	mov ecx, 1376
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 192
	mov ecx, 1408
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 32
210:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+1152]
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
	jne 210b
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
211:
	sub esi, 1
	cmp esi, 36
	je 212f
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
	jmp 213f
212:
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
213:
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
	je 214f
	mov eax, esi
	mov ecx, 7
	mul ecx
	mov ecx, eax
	add ecx, edi
	movzx eax, BYTE PTR [ecx+4102]
	sub eax, 1
	mov ecx, eax
	jmp 215f
214:
	mov ecx, -1
215:
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
	jne 211b
	mov eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+1376], eax
	mov eax, DWORD PTR [edi+516]
	mov DWORD PTR [edi+1380], eax
	mov eax, DWORD PTR [edi+520]
	mov DWORD PTR [edi+1384], eax
	mov eax, DWORD PTR [edi+524]
	mov DWORD PTR [edi+1388], eax
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [edi+1392], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [edi+1396], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [edi+1400], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [edi+1404], eax
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+1408], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+1412], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+1416], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+1420], eax
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [edi+1424], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [edi+1428], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [edi+1432], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [edi+1436], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+1268], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+1272], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+1276], eax
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
	mov esi, 32
216:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+1184]
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
	jne 216b
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+796], eax
	mov esi, 0
	mov eax, esi
	mov ecx, 96
	mul ecx
	mov edx, edi
	add edx, 4876
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+704]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+720]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+736]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+752]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+768]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+784]
	movdqu XMMWORD PTR [edx+80], xmm5
	mov eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [edi+1440]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+1444]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+1448]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+1452]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+1440]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+1444]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+1448]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+1452]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+700], eax
	mov esi, 1
	mov eax, esi
	mov ecx, 96
	mul ecx
	mov edx, edi
	add edx, 4876
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+704]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+720]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+736]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+752]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+768]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+784]
	movdqu XMMWORD PTR [edx+80], xmm5
217:
	mov eax, 1280
	mov ecx, 608
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
	mov eax, 1440
	mov ecx, 640
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
	mov eax, 224
	mov ecx, 672
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
	mov eax, 640
	mov ecx, 608
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
	mov eax, 1440
	mov ecx, 1280
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
	mov eax, 672
	mov ecx, 608
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
	mov eax, 224
	mov ecx, 1280
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
	mov eax, 672
	mov ecx, 640
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
	mov eax, 224
	mov ecx, 1440
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
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
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
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
	mov edx, 768
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
	mov ecx, 288
	mov edx, 704
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
	mov ecx, 704
	mov edx, 768
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
	mov ecx, 832
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 832
	mov edx, 768
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
	mov edx, 736
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
	mov ecx, 288
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
	mov ecx, 736
	mov edx, 736
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
	mov eax, 704
	mov ecx, 896
	mov edx, 704
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
	mov ecx, 704
	mov edx, 704
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
	mov eax, 768
	mov ecx, 960
	mov edx, 768
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
	mov ecx, 768
	mov edx, 768
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	add esi, 1
	mov eax, esi
	mov ecx, 96
	mul ecx
	mov edx, edi
	add edx, 4876
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+704]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+720]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+736]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+752]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+768]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+784]
	movdqu XMMWORD PTR [edx+80], xmm5
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [edi+660], eax
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
	mov eax, DWORD PTR [edi+784]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+788]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+792]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+796]
	mov DWORD PTR [edi+700], eax
	cmp esi, 15
	jne 217b
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+540], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+604], eax
	mov esi, 64
218:
	sub esi, 1
	mov eax, 576
	mov ecx, 512
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
	mov eax, 576
	mov ecx, 576
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
	mov ecx, 544
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
	mov eax, 160
	mov ecx, 576
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
	mov eax, 608
	mov ecx, 608
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
	mov eax, 640
	mov ecx, 640
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
	mov eax, 832
	mov ecx, 832
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
	mov eax, 832
	mov ecx, 608
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
	mov eax, 896
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
	mov eax, 800
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
	mov eax, 864
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
	mov eax, 896
	mov ecx, 896
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
	mov eax, 672
	mov ecx, 672
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
	mov eax, 928
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
	mov eax, 928
	mov ecx, 256
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
	mov eax, 800
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
	mov eax, 800
	mov ecx, 960
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
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 640
	mov edx, 768
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
	mov ecx, 768
	mov edx, 768
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
	mov ecx, 928
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 704
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 704
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 896
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 928
	mov edx, 736
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
	mov ecx, 864
	mov edx, 864
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
	mov ecx, 864
	mov edx, 864
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
	mov ecx, 864
	mov edx, 864
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
	mov ecx, 736
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 704
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
	mov ecx, 736
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
	mov eax, 832
	mov ecx, 832
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
	mov eax, 832
	mov ecx, 704
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
	mov eax, 896
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
	mov eax, 800
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
	mov eax, 864
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
	mov eax, 896
	mov ecx, 896
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
	mov eax, 768
	mov ecx, 768
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
	mov eax, 928
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
	mov eax, 928
	mov ecx, 256
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
	mov eax, 800
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
	mov eax, 800
	mov ecx, 960
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
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 736
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
	mov eax, 672
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
	mov eax, 928
	mov ecx, 928
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
	mov eax, 896
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
	mov eax, 896
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
	mov eax, 608
	mov ecx, 896
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 928
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
	mov eax, 864
	mov ecx, 864
	mov edx, 864
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
	mov ecx, 864
	mov edx, 864
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
	mov ecx, 864
	mov edx, 864
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
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 608
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
	mov eax, 640
	mov ecx, 640
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
	mov eax, 832
	mov ecx, 832
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
	mov eax, 832
	mov ecx, 608
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
	mov eax, 896
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
	mov eax, 800
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
	mov eax, 864
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
	mov eax, 896
	mov ecx, 896
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
	mov eax, 672
	mov ecx, 672
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
	mov eax, 928
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
	mov eax, 928
	mov ecx, 256
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
	mov eax, 800
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
	mov eax, 800
	mov ecx, 960
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
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 640
	mov edx, 768
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
	mov ecx, 768
	mov edx, 768
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
	mov ecx, 928
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 704
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 704
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 896
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 928
	mov edx, 736
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
	mov ecx, 864
	mov edx, 864
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
	mov ecx, 864
	mov edx, 864
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
	mov ecx, 864
	mov edx, 864
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
	mov ecx, 736
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 704
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
	mov ecx, 736
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
	mov eax, 832
	mov ecx, 832
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
	mov eax, 832
	mov ecx, 704
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
	mov eax, 896
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
	mov eax, 800
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
	mov eax, 864
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
	mov eax, 896
	mov ecx, 896
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
	mov eax, 768
	mov ecx, 768
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
	mov eax, 928
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
	mov eax, 928
	mov ecx, 256
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
	mov eax, 800
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
	mov eax, 800
	mov ecx, 960
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
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 736
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
	mov eax, 672
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
	mov eax, 928
	mov ecx, 928
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
	mov eax, 896
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
	mov eax, 896
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
	mov eax, 608
	mov ecx, 896
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 928
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
	mov eax, 864
	mov ecx, 864
	mov edx, 864
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
	mov ecx, 864
	mov edx, 864
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
	mov ecx, 864
	mov edx, 864
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
	mov ecx, 640
	mov edx, 640
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
	mov ecx, 608
	mov edx, 512
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
	mov ecx, 672
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
	mov ecx, 800
	mov edx, 576
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 160
	mov ecx, 640
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
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
	mov ecx, edx
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+544]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+548]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+552]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+556]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+560]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+564]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+568]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+572]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+572], eax
	cmp esi, 63
	je 219f
	mov eax, esi
	mov ecx, 4
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
	jmp 220f
219:
	mov eax, esi
	mov ecx, 4
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
220:
	mov ebx, eax
	add ebx, 1
	mov edx, edi
	add edx, 4876
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
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
	movdqu xmm6, XMMWORD PTR [edx+64]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+80]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 2
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+96]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+112]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+128]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+144]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+160]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+176]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 3
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
	movdqu xmm6, XMMWORD PTR [edx+256]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+272]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 4
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+288]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+304]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+320]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+336]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+352]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+368]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 5
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
	movdqu xmm6, XMMWORD PTR [edx+448]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+464]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 6
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+480]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+496]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+512]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+528]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+544]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+560]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 7
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
	movdqu xmm6, XMMWORD PTR [edx+640]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+656]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 8
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+672]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+688]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+704]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+720]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+736]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+752]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 9
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
	movdqu xmm6, XMMWORD PTR [edx+832]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+848]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 10
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+864]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+880]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+896]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+912]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+928]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+944]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 11
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
	movdqu xmm6, XMMWORD PTR [edx+1024]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1040]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 12
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1056]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1072]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1088]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1104]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1120]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1136]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 13
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
	movdqu xmm6, XMMWORD PTR [edx+1216]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1232]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 14
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1248]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1264]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1280]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1296]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1312]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1328]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 15
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
	movdqu xmm6, XMMWORD PTR [edx+1408]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1424]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 16
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1440]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1456]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1472]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1488]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1504]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1520]
	pand xmm6, xmm7
	por xmm5, xmm6
	movdqu XMMWORD PTR [edi+704], xmm0
	movdqu XMMWORD PTR [edi+720], xmm1
	movdqu XMMWORD PTR [edi+736], xmm2
	movdqu XMMWORD PTR [edi+752], xmm3
	movdqu XMMWORD PTR [edi+768], xmm4
	movdqu XMMWORD PTR [edi+784], xmm5
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
	mov ecx, 288
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
	mov ecx, 288
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
	jne 218b
	mov eax, 512
	mov ecx, 1376
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
	mov eax, 544
	mov ecx, 1408
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
	mov eax, 576
	mov ecx, 1248
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
	mov eax, 1408
	mov ecx, 1376
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
	mov eax, 544
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
	mov eax, 1248
	mov ecx, 1376
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
	mov eax, 576
	mov ecx, 512
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
	mov eax, 1248
	mov ecx, 1408
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
	mov eax, 576
	mov ecx, 544
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
	mov ecx, 288
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
	mov ecx, 288
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
	mov eax, -1505338516
	mov DWORD PTR [edi+1152], eax
	mov eax, -1929453701
	mov DWORD PTR [edi+1156], eax
	mov eax, 1632456525
	mov DWORD PTR [edi+1160], eax
	mov eax, 1557023782
	mov DWORD PTR [edi+1164], eax
	mov eax, 1796917255
	mov DWORD PTR [edi+1168], eax
	mov eax, -1578313011
	mov DWORD PTR [edi+1172], eax
	mov eax, -443187288
	mov DWORD PTR [edi+1176], eax
	mov eax, 1192733217
	mov DWORD PTR [edi+1180], eax
	mov eax, -204820319
	mov DWORD PTR [edi+992], eax
	mov eax, -1944042765
	mov DWORD PTR [edi+996], eax
	mov eax, 1735657585
	mov DWORD PTR [edi+1000], eax
	mov eax, 873885225
	mov DWORD PTR [edi+1004], eax
	mov eax, 1153993462
	mov DWORD PTR [edi+1008], eax
	mov eax, -1480785032
	mov DWORD PTR [edi+1012], eax
	mov eax, 671998333
	mov DWORD PTR [edi+1016], eax
	mov eax, 418776653
	mov DWORD PTR [edi+1020], eax
	mov eax, -2010776368
	mov DWORD PTR [edi+96], eax
	mov eax, -1879754342
	mov DWORD PTR [edi+100], eax
	mov eax, 532969776
	mov DWORD PTR [edi+104], eax
	mov eax, -503153792
	mov DWORD PTR [edi+108], eax
	mov eax, 0
	mov DWORD PTR [edi+112], eax
	mov eax, 0
	mov DWORD PTR [edi+116], eax
	mov eax, 0
	mov DWORD PTR [edi+120], eax
	mov eax, 0
	mov DWORD PTR [edi+124], eax
	mov eax, 1152
	mov ecx, 1056
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
	mov eax, 576
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
	mov eax, 1184
	mov ecx, 512
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 992
	mov ecx, 1152
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
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
	mov eax, 1184
	mov ecx, 512
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1344]
	or edx, DWORD PTR [edi+1348]
	or edx, DWORD PTR [edi+1352]
	or edx, DWORD PTR [edi+1356]
	or edx, DWORD PTR [edi+1360]
	or edx, DWORD PTR [edi+1364]
	or edx, DWORD PTR [edi+1368]
	or edx, DWORD PTR [edi+1372]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov ebx, edx
	mov edx, DWORD PTR [edi+1056]
	sub edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+1060]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+1064]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+1068]
	sbb edx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+1072]
	sbb edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+1076]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+1080]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+1084]
	sbb edx, DWORD PTR [edi+124]
	sbb eax, eax
	mov edx, DWORD PTR [edi+1280]
	or edx, DWORD PTR [edi+1284]
	or edx, DWORD PTR [edi+1288]
	or edx, DWORD PTR [edi+1292]
	or edx, DWORD PTR [edi+1296]
	or edx, DWORD PTR [edi+1300]
	or edx, DWORD PTR [edi+1304]
	or edx, DWORD PTR [edi+1308]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	and edx, eax
	or edx, ebx
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
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	lea esp, [esp+108]
	pxor xmm0, xmm0
	lea esp, [esp-128]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	movdqu XMMWORD PTR [esp+112], xmm0
	lea esp, [esp+128]
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

vg_ecdsa_brainpoolp256r1_sign:
	lea esp, [esp-512]
	mov DWORD PTR [esp+128], ebx
	mov DWORD PTR [esp+132], esi
	mov DWORD PTR [esp+136], edi
	mov DWORD PTR [esp+140], ebp
	mov eax, DWORD PTR [esp+536]
	mov ecx, DWORD PTR [eax+16]
	mov DWORD PTR [esp+144], ecx
	mov ecx, DWORD PTR [eax+20]
	mov DWORD PTR [esp+148], ecx
	mov eax, 0
	mov DWORD PTR [esp+232], eax
	mov DWORD PTR [esp+236], eax
	mov DWORD PTR [esp+240], eax
	mov DWORD PTR [esp+244], eax
	mov DWORD PTR [esp+248], eax
	mov DWORD PTR [esp+252], eax
	mov DWORD PTR [esp+256], eax
	mov DWORD PTR [esp+260], eax
	mov DWORD PTR [esp+264], eax
	mov DWORD PTR [esp+268], eax
	mov DWORD PTR [esp+272], eax
	mov DWORD PTR [esp+276], eax
	mov DWORD PTR [esp+280], eax
	mov DWORD PTR [esp+284], eax
	mov DWORD PTR [esp+288], eax
	mov DWORD PTR [esp+292], eax
	mov DWORD PTR [esp+296], eax
	mov DWORD PTR [esp+300], eax
	mov ecx, DWORD PTR [esp+144]
	sub ecx, 32
	sbb edx, edx
	and ecx, edx
	add ecx, 32
	mov ebx, esp
	add ebx, 264
	sub ebx, ecx
	mov esi, DWORD PTR [esp+524]
20:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 20b
	mov esi, esp
	add esi, 232
	mov eax, DWORD PTR [esi+28]
	bswap eax
	mov DWORD PTR [esp+188], eax
	sub eax, -1756866905
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esi+24]
	bswap eax
	mov DWORD PTR [esp+184], eax
	sbb eax, -1877078398
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esi+20]
	bswap eax
	mov DWORD PTR [esp+180], eax
	sbb eax, -1251891465
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esi+16]
	bswap eax
	mov DWORD PTR [esp+176], eax
	sbb eax, -1942390109
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [esp+172], eax
	sbb eax, -1652322959
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [esp+168], eax
	sbb eax, 1046874768
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [esp+164], eax
	sbb eax, -1578194500
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [esp+160], eax
	sbb eax, -1443145765
	mov DWORD PTR [esp], eax
	sbb edx, edx
	mov eax, DWORD PTR [esp+188]
	mov ecx, DWORD PTR [esp+28]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+188], eax
	mov eax, DWORD PTR [esp+184]
	mov ecx, DWORD PTR [esp+24]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+184], eax
	mov eax, DWORD PTR [esp+180]
	mov ecx, DWORD PTR [esp+20]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+180], eax
	mov eax, DWORD PTR [esp+176]
	mov ecx, DWORD PTR [esp+16]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+176], eax
	mov eax, DWORD PTR [esp+172]
	mov ecx, DWORD PTR [esp+12]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+172], eax
	mov eax, DWORD PTR [esp+168]
	mov ecx, DWORD PTR [esp+8]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+168], eax
	mov eax, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+4]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+164], eax
	mov eax, DWORD PTR [esp+160]
	mov ecx, DWORD PTR [esp]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+160], eax
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
	mov edi, DWORD PTR [esp+532]
	mov esi, DWORD PTR [esp+520]
	mov eax, 0
	mov BYTE PTR [edi+3792], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+3793], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+3797], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+3801], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+3805], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+3809], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+3813], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+3817], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+3821], eax
	mov eax, DWORD PTR [esp+160]
	mov DWORD PTR [edi+3825], eax
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [edi+3829], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [edi+3833], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [edi+3837], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [edi+3841], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [edi+3845], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [edi+3849], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [edi+3853], eax
	mov edi, DWORD PTR [esp+532]
	add edi, 0
	mov esi, DWORD PTR [esp+532]
	add esi, 192
	mov edx, esp
	add edx, 0
	mov ecx, DWORD PTR [esp+144]
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+532]
	add edi, 0
	mov esi, DWORD PTR [esp+148]
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, DWORD PTR [esp+144]
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+4]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+532]
	add edi, 0
	mov esi, DWORD PTR [esp+148]
	add esi, DWORD PTR [esp+144]
	mov eax, 0
	mov edx, DWORD PTR [esp+532]
	add edx, 3792
	mov ecx, 65
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+4]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+532]
	add edx, 0
	mov esi, DWORD PTR [esp+532]
	add esi, 192
	mov eax, DWORD PTR [esp+148]
	add eax, DWORD PTR [esp+144]
	add eax, 65
	mov ecx, 0
	mov edi, esp
	add edi, 0
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+8]
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+532]
	add edi, 0
	mov esi, DWORD PTR [esp+532]
	add esi, 192
	mov edx, esp
	add edx, 0
	mov ecx, DWORD PTR [esp+144]
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [esp+532]
	add esi, 0
	mov ebx, DWORD PTR [esp+532]
	add ebx, 4608
	mov ecx, 384
21:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 21b
	mov edi, DWORD PTR [esp+532]
	add edi, 0
	mov esi, DWORD PTR [esp+148]
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, DWORD PTR [esp+144]
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+4]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+532]
	add edx, 0
	mov esi, DWORD PTR [esp+532]
	add esi, 192
	mov eax, DWORD PTR [esp+148]
	add eax, DWORD PTR [esp+144]
	add eax, 0
	mov ecx, 0
	mov edi, esp
	add edi, 64
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+8]
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+532]
	mov esi, DWORD PTR [esp+520]
	mov eax, 1
	mov BYTE PTR [edi+3792], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+3793], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+3797], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+3801], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+3805], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+3809], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+3813], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+3817], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+3821], eax
	mov eax, DWORD PTR [esp+160]
	mov DWORD PTR [edi+3825], eax
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [edi+3829], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [edi+3833], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [edi+3837], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [edi+3841], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [edi+3845], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [edi+3849], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [edi+3853], eax
	mov esi, DWORD PTR [esp+532]
	add esi, 4608
	mov ebx, DWORD PTR [esp+532]
	add ebx, 0
	mov ecx, 384
22:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 22b
	mov edi, DWORD PTR [esp+532]
	add edi, 0
	mov esi, DWORD PTR [esp+148]
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, DWORD PTR [esp+144]
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+4]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+532]
	add edi, 0
	mov esi, DWORD PTR [esp+148]
	add esi, DWORD PTR [esp+144]
	mov eax, 0
	mov edx, DWORD PTR [esp+532]
	add edx, 3792
	mov ecx, 65
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+4]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+532]
	add edx, 0
	mov esi, DWORD PTR [esp+532]
	add esi, 192
	mov eax, DWORD PTR [esp+148]
	add eax, DWORD PTR [esp+144]
	add eax, 65
	mov ecx, 0
	mov edi, esp
	add edi, 0
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+8]
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+532]
	add edi, 0
	mov esi, DWORD PTR [esp+532]
	add esi, 192
	mov edx, esp
	add edx, 0
	mov ecx, DWORD PTR [esp+144]
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [esp+532]
	add esi, 0
	mov ebx, DWORD PTR [esp+532]
	add ebx, 4608
	mov ecx, 384
23:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 23b
	mov edi, DWORD PTR [esp+532]
	add edi, 0
	mov esi, DWORD PTR [esp+148]
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, DWORD PTR [esp+144]
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+4]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+532]
	add edx, 0
	mov esi, DWORD PTR [esp+532]
	add esi, 192
	mov eax, DWORD PTR [esp+148]
	add eax, DWORD PTR [esp+144]
	add eax, 0
	mov ecx, 0
	mov edi, esp
	add edi, 64
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+8]
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 128
	mov DWORD PTR [esp+156], eax
24:
	mov eax, 0
	mov DWORD PTR [esp+152], eax
25:
	mov esi, DWORD PTR [esp+532]
	add esi, 4608
	mov ebx, DWORD PTR [esp+532]
	add ebx, 0
	mov ecx, 384
26:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 26b
	mov edi, DWORD PTR [esp+532]
	add edi, 0
	mov esi, DWORD PTR [esp+148]
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, DWORD PTR [esp+144]
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+4]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+532]
	add edx, 0
	mov esi, DWORD PTR [esp+532]
	add esi, 192
	mov eax, DWORD PTR [esp+148]
	add eax, DWORD PTR [esp+144]
	add eax, 0
	mov ecx, 0
	mov edi, esp
	add edi, 64
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+8]
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, esp
	add esi, 64
	mov ebx, esp
	add ebx, 376
	add ebx, DWORD PTR [esp+152]
	mov ecx, DWORD PTR [esp+144]
27:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 27b
	mov eax, DWORD PTR [esp+152]
	add eax, DWORD PTR [esp+144]
	mov DWORD PTR [esp+152], eax
	cmp eax, 32
	jb 25b
	mov edi, DWORD PTR [esp+516]
	mov esi, DWORD PTR [esp+520]
	mov edx, esp
	add edx, 232
	mov ecx, esp
	add ecx, 376
	mov ebp, DWORD PTR [esp+532]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_brainpoolp256r1_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+156]
	sub ecx, 1
	mov DWORD PTR [esp+156], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 28f
	mov edx, 0
	test edx, edx
	jmp 29f
28:
	mov edi, DWORD PTR [esp+532]
	mov esi, DWORD PTR [esp+520]
	mov eax, 0
	mov BYTE PTR [edi+3792], al
	mov edi, DWORD PTR [esp+532]
	add edi, 0
	mov esi, DWORD PTR [esp+532]
	add esi, 192
	mov edx, esp
	add edx, 0
	mov ecx, DWORD PTR [esp+144]
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+532]
	add edi, 0
	mov esi, DWORD PTR [esp+148]
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, DWORD PTR [esp+144]
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+4]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+532]
	add edi, 0
	mov esi, DWORD PTR [esp+148]
	add esi, DWORD PTR [esp+144]
	mov eax, 0
	mov edx, DWORD PTR [esp+532]
	add edx, 3792
	mov ecx, 1
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+4]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+532]
	add edx, 0
	mov esi, DWORD PTR [esp+532]
	add esi, 192
	mov eax, DWORD PTR [esp+148]
	add eax, DWORD PTR [esp+144]
	add eax, 1
	mov ecx, 0
	mov edi, esp
	add edi, 0
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+8]
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+532]
	add edi, 0
	mov esi, DWORD PTR [esp+532]
	add esi, 192
	mov edx, esp
	add edx, 0
	mov ecx, DWORD PTR [esp+144]
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [esp+532]
	add esi, 0
	mov ebx, DWORD PTR [esp+532]
	add ebx, 4608
	mov ecx, 384
210:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 210b
	mov edi, DWORD PTR [esp+532]
	add edi, 0
	mov esi, DWORD PTR [esp+148]
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, DWORD PTR [esp+144]
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+4]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+532]
	add edx, 0
	mov esi, DWORD PTR [esp+532]
	add esi, 192
	mov eax, DWORD PTR [esp+148]
	add eax, DWORD PTR [esp+144]
	add eax, 0
	mov ecx, 0
	mov edi, esp
	add edi, 64
	mov ebp, DWORD PTR [esp+532]
	add ebp, 384
	mov ebx, DWORD PTR [esp+536]
	mov ebx, DWORD PTR [ebx+8]
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call ebx
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, 1
	test edx, edx
29:
	jne 24b
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
	mov ebx, DWORD PTR [esp+128]
	mov esi, DWORD PTR [esp+132]
	mov edi, DWORD PTR [esp+136]
	mov ebp, DWORD PTR [esp+140]
	lea esp, [esp+512]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-612]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	movdqu XMMWORD PTR [esp+112], xmm0
	movdqu XMMWORD PTR [esp+128], xmm0
	movdqu XMMWORD PTR [esp+144], xmm0
	movdqu XMMWORD PTR [esp+160], xmm0
	movdqu XMMWORD PTR [esp+176], xmm0
	movdqu XMMWORD PTR [esp+192], xmm0
	movdqu XMMWORD PTR [esp+208], xmm0
	movdqu XMMWORD PTR [esp+224], xmm0
	movdqu XMMWORD PTR [esp+240], xmm0
	movdqu XMMWORD PTR [esp+256], xmm0
	movdqu XMMWORD PTR [esp+272], xmm0
	movdqu XMMWORD PTR [esp+288], xmm0
	movdqu XMMWORD PTR [esp+304], xmm0
	movdqu XMMWORD PTR [esp+320], xmm0
	movdqu XMMWORD PTR [esp+336], xmm0
	movdqu XMMWORD PTR [esp+352], xmm0
	movdqu XMMWORD PTR [esp+368], xmm0
	movdqu XMMWORD PTR [esp+384], xmm0
	movdqu XMMWORD PTR [esp+400], xmm0
	movdqu XMMWORD PTR [esp+416], xmm0
	movdqu XMMWORD PTR [esp+432], xmm0
	movdqu XMMWORD PTR [esp+448], xmm0
	movdqu XMMWORD PTR [esp+464], xmm0
	movdqu XMMWORD PTR [esp+480], xmm0
	movdqu XMMWORD PTR [esp+496], xmm0
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	mov DWORD PTR [esp+608], ecx
	lea esp, [esp+612]
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
