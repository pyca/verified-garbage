// The functions of `src/internal/vg_ecdsa_brainpoolp256r1_sign.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp256r1_sign:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+16]
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
	mov ebx, DWORD PTR [esp+12]
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
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3580], eax
	mov esi, 256
23:
	sub esi, 1
	mov eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+516]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+520]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+524]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+3420], eax
	push edi
	call {vg_brainpoolp256r1_point_double}
	pop eax
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+3420], eax
	push edi
	call {vg_brainpoolp256r1_point_add}
	pop eax
	mov edi, DWORD PTR [esp+20]
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4096]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+3328]
	mov edx, DWORD PTR [edi+3232]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+3332]
	mov edx, DWORD PTR [edi+3236]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+3336]
	mov edx, DWORD PTR [edi+3240]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+3340]
	mov edx, DWORD PTR [edi+3244]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+3344]
	mov edx, DWORD PTR [edi+3248]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+3348]
	mov edx, DWORD PTR [edi+3252]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+3352]
	mov edx, DWORD PTR [edi+3256]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+3356]
	mov edx, DWORD PTR [edi+3260]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+540], eax
	mov eax, DWORD PTR [edi+3360]
	mov edx, DWORD PTR [edi+3264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+3364]
	mov edx, DWORD PTR [edi+3268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+3368]
	mov edx, DWORD PTR [edi+3272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+3372]
	mov edx, DWORD PTR [edi+3276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+3376]
	mov edx, DWORD PTR [edi+3280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+3380]
	mov edx, DWORD PTR [edi+3284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+3384]
	mov edx, DWORD PTR [edi+3288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+3388]
	mov edx, DWORD PTR [edi+3292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+3392]
	mov edx, DWORD PTR [edi+3296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+3396]
	mov edx, DWORD PTR [edi+3300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+3400]
	mov edx, DWORD PTR [edi+3304]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+3404]
	mov edx, DWORD PTR [edi+3308]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+3408]
	mov edx, DWORD PTR [edi+3312]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+3412]
	mov edx, DWORD PTR [edi+3316]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+3416]
	mov edx, DWORD PTR [edi+3320]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+3420]
	mov edx, DWORD PTR [edi+3324]
	xor edx, eax
	and edx, ecx
	xor eax, edx
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
24:
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
25:
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
	jne 25b
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
	jne 24b
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
	mov eax, 160
	mov ecx, 1184
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 384
	mov ecx, 1056
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
	mov edx, DWORD PTR [edi+1216]
	or edx, DWORD PTR [edi+1220]
	or edx, DWORD PTR [edi+1224]
	or edx, DWORD PTR [edi+1228]
	or edx, DWORD PTR [edi+1232]
	or edx, DWORD PTR [edi+1236]
	or edx, DWORD PTR [edi+1240]
	or edx, DWORD PTR [edi+1244]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
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
26:
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
27:
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
	jne 27b
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
	jne 26b
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
	mov ecx, 1216
	mov edx, 1280
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
	mov eax, 384
	mov ecx, 1120
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
	mov eax, 1312
	mov ecx, 1280
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
	mov eax, 1344
	mov ecx, 1376
	mov edx, 1376
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_add_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1376
	mov ecx, 992
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
	mov ecx, 1408
	mov edx, 1440
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp256r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1440]
	or edx, DWORD PTR [edi+1444]
	or edx, DWORD PTR [edi+1448]
	or edx, DWORD PTR [edi+1452]
	or edx, DWORD PTR [edi+1456]
	or edx, DWORD PTR [edi+1460]
	or edx, DWORD PTR [edi+1464]
	or edx, DWORD PTR [edi+1468]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov ecx, DWORD PTR [edi+1472]
	mov ebx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+1216]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+28], eax
	mov eax, DWORD PTR [edi+1220]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+24], eax
	mov eax, DWORD PTR [edi+1224]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+20], eax
	mov eax, DWORD PTR [edi+1228]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+16], eax
	mov eax, DWORD PTR [edi+1232]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+12], eax
	mov eax, DWORD PTR [edi+1236]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [edi+1240]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [edi+1244]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [edi+1440]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [edi+1444]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+56], eax
	mov eax, DWORD PTR [edi+1448]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+52], eax
	mov eax, DWORD PTR [edi+1452]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+48], eax
	mov eax, DWORD PTR [edi+1456]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+44], eax
	mov eax, DWORD PTR [edi+1460]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+40], eax
	mov eax, DWORD PTR [edi+1464]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+36], eax
	mov eax, DWORD PTR [edi+1468]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+32], eax
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	ret
	.p2align 6
