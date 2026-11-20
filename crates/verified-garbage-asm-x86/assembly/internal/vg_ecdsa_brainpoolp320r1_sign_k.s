// The functions of `src/internal/vg_ecdsa_brainpoolp320r1_sign_k.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp320r1_sign_k:
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_BRAINPOOLP320R1_COMB}
	pop ecx
	mov edx, DWORD PTR [esp+20]
	mov DWORD PTR [edx+60], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+16]
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1304], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1308], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1312], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1316], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1320], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1324], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1328], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1332], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1336], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1340], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1344], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1348], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1352], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1356], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1360], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1364], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1368], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1372], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1376], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1380], eax
	mov ebx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1384], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1388], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1392], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1396], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1400], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1404], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1408], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1412], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1416], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1420], eax
	mov eax, -239915481
	mov DWORD PTR [edi+64], eax
	mov eax, -53210447
	mov DWORD PTR [edi+68], eax
	mov eax, 2022960168
	mov DWORD PTR [edi+72], eax
	mov eax, 1335015916
	mov DWORD PTR [edi+76], eax
	mov eax, -151777809
	mov DWORD PTR [edi+80], eax
	mov eax, -108015706
	mov DWORD PTR [edi+84], eax
	mov eax, -771628955
	mov DWORD PTR [edi+88], eax
	mov eax, -516130722
	mov DWORD PTR [edi+92], eax
	mov eax, 918310839
	mov DWORD PTR [edi+96], eax
	mov eax, -748796128
	mov DWORD PTR [edi+100], eax
	mov eax, 1153798929
	mov DWORD PTR [edi+104], eax
	mov eax, -2037295781
	mov DWORD PTR [edi+108], eax
	mov eax, -293185303
	mov DWORD PTR [edi+112], eax
	mov eax, 759705287
	mov DWORD PTR [edi+116], eax
	mov eax, -1232137565
	mov DWORD PTR [edi+120], eax
	mov eax, -108015707
	mov DWORD PTR [edi+124], eax
	mov eax, -771628955
	mov DWORD PTR [edi+128], eax
	mov eax, -516130722
	mov DWORD PTR [edi+132], eax
	mov eax, 918310839
	mov DWORD PTR [edi+136], eax
	mov eax, -748796128
	mov DWORD PTR [edi+140], eax
	mov eax, 0
	mov DWORD PTR [edi+184], eax
	mov eax, 0
	mov DWORD PTR [edi+188], eax
	mov eax, 0
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
	mov eax, 1
	mov DWORD PTR [edi+224], eax
	mov eax, 0
	mov DWORD PTR [edi+228], eax
	mov eax, 0
	mov DWORD PTR [edi+232], eax
	mov eax, 0
	mov DWORD PTR [edi+236], eax
	mov eax, 0
	mov DWORD PTR [edi+240], eax
	mov eax, 0
	mov DWORD PTR [edi+244], eax
	mov eax, 0
	mov DWORD PTR [edi+248], eax
	mov eax, 0
	mov DWORD PTR [edi+252], eax
	mov eax, 0
	mov DWORD PTR [edi+256], eax
	mov eax, 0
	mov DWORD PTR [edi+260], eax
	mov eax, 239915481
	mov DWORD PTR [edi+264], eax
	mov eax, 53210446
	mov DWORD PTR [edi+268], eax
	mov eax, -2022960169
	mov DWORD PTR [edi+272], eax
	mov eax, -1335015917
	mov DWORD PTR [edi+276], eax
	mov eax, 151777808
	mov DWORD PTR [edi+280], eax
	mov eax, 108015705
	mov DWORD PTR [edi+284], eax
	mov eax, 771628954
	mov DWORD PTR [edi+288], eax
	mov eax, 516130721
	mov DWORD PTR [edi+292], eax
	mov eax, -918310840
	mov DWORD PTR [edi+296], eax
	mov eax, 748796127
	mov DWORD PTR [edi+300], eax
	mov eax, 259077538
	mov DWORD PTR [edi+304], eax
	mov eax, 548663931
	mov DWORD PTR [edi+308], eax
	mov eax, -1547509882
	mov DWORD PTR [edi+312], eax
	mov eax, 66349677
	mov DWORD PTR [edi+316], eax
	mov eax, -1147621357
	mov DWORD PTR [edi+320], eax
	mov eax, -1590058015
	mov DWORD PTR [edi+324], eax
	mov eax, -840223009
	mov DWORD PTR [edi+328], eax
	mov eax, 976591080
	mov DWORD PTR [edi+332], eax
	mov eax, -826106522
	mov DWORD PTR [edi+336], eax
	mov eax, 1182513337
	mov DWORD PTR [edi+340], eax
	mov eax, 1550791936
	mov DWORD PTR [edi+344], eax
	mov eax, 1642259846
	mov DWORD PTR [edi+348], eax
	mov eax, 1885706431
	mov DWORD PTR [edi+352], eax
	mov eax, -1626685503
	mov DWORD PTR [edi+356], eax
	mov eax, -718237428
	mov DWORD PTR [edi+360], eax
	mov eax, 1441072705
	mov DWORD PTR [edi+364], eax
	mov eax, -1009565093
	mov DWORD PTR [edi+368], eax
	mov eax, -235477864
	mov DWORD PTR [edi+372], eax
	mov eax, 253778633
	mov DWORD PTR [edi+376], eax
	mov eax, 317161758
	mov DWORD PTR [edi+380], eax
	mov eax, 1568410297
	mov DWORD PTR [edi+384], eax
	mov eax, -1114481040
	mov DWORD PTR [edi+388], eax
	mov eax, -556994309
	mov DWORD PTR [edi+392], eax
	mov eax, -294584668
	mov DWORD PTR [edi+396], eax
	mov eax, 486380446
	mov DWORD PTR [edi+400], eax
	mov eax, 1881865264
	mov DWORD PTR [edi+404], eax
	mov eax, -1085136397
	mov DWORD PTR [edi+408], eax
	mov eax, 1448078851
	mov DWORD PTR [edi+412], eax
	mov eax, 1102312676
	mov DWORD PTR [edi+416], eax
	mov eax, 1148123315
	mov DWORD PTR [edi+420], eax
	mov eax, 1204576588
	mov DWORD PTR [edi+424], eax
	mov eax, 1409365895
	mov DWORD PTR [edi+428], eax
	mov eax, -2145459591
	mov DWORD PTR [edi+432], eax
	mov eax, -964721145
	mov DWORD PTR [edi+436], eax
	mov eax, -1354822665
	mov DWORD PTR [edi+440], eax
	mov eax, 1410548566
	mov DWORD PTR [edi+444], eax
	mov eax, -2115649927
	mov DWORD PTR [edi+448], eax
	mov eax, -76932575
	mov DWORD PTR [edi+452], eax
	mov eax, -1116427382
	mov DWORD PTR [edi+456], eax
	mov eax, 1989841794
	mov DWORD PTR [edi+460], eax
	mov eax, 622060749
	mov DWORD PTR [edi+464], eax
	mov eax, 1738353119
	mov DWORD PTR [edi+468], eax
	mov eax, -522098683
	mov DWORD PTR [edi+472], eax
	mov eax, -1849491429
	mov DWORD PTR [edi+476], eax
	mov eax, -1350122487
	mov DWORD PTR [edi+480], eax
	mov eax, -2035076932
	mov DWORD PTR [edi+484], eax
	mov eax, 1315148030
	mov DWORD PTR [edi+488], eax
	mov eax, -485673692
	mov DWORD PTR [edi+492], eax
	mov eax, 838906191
	mov DWORD PTR [edi+496], eax
	mov eax, 837584839
	mov DWORD PTR [edi+500], eax
	mov eax, -1153798929
	mov DWORD PTR [edi+504], eax
	mov eax, 2037295780
	mov DWORD PTR [edi+508], eax
	mov eax, 293185302
	mov DWORD PTR [edi+512], eax
	mov eax, -759705288
	mov DWORD PTR [edi+516], eax
	mov eax, 1232137564
	mov DWORD PTR [edi+520], eax
	mov eax, 108015706
	mov DWORD PTR [edi+524], eax
	mov eax, 771628954
	mov DWORD PTR [edi+528], eax
	mov eax, 516130721
	mov DWORD PTR [edi+532], eax
	mov eax, -918310840
	mov DWORD PTR [edi+536], eax
	mov eax, 748796127
	mov DWORD PTR [edi+540], eax
	mov eax, -239915483
	mov DWORD PTR [edi+544], eax
	mov eax, -53210447
	mov DWORD PTR [edi+548], eax
	mov eax, 2022960168
	mov DWORD PTR [edi+552], eax
	mov eax, 1335015916
	mov DWORD PTR [edi+556], eax
	mov eax, -151777809
	mov DWORD PTR [edi+560], eax
	mov eax, -108015706
	mov DWORD PTR [edi+564], eax
	mov eax, -771628955
	mov DWORD PTR [edi+568], eax
	mov eax, -516130722
	mov DWORD PTR [edi+572], eax
	mov eax, 918310839
	mov DWORD PTR [edi+576], eax
	mov eax, -748796128
	mov DWORD PTR [edi+580], eax
	mov eax, 1153798927
	mov DWORD PTR [edi+584], eax
	mov eax, -2037295781
	mov DWORD PTR [edi+588], eax
	mov eax, -293185303
	mov DWORD PTR [edi+592], eax
	mov eax, 759705287
	mov DWORD PTR [edi+596], eax
	mov eax, -1232137565
	mov DWORD PTR [edi+600], eax
	mov eax, -108015707
	mov DWORD PTR [edi+604], eax
	mov eax, -771628955
	mov DWORD PTR [edi+608], eax
	mov eax, -516130722
	mov DWORD PTR [edi+612], eax
	mov eax, 918310839
	mov DWORD PTR [edi+616], eax
	mov eax, -748796128
	mov DWORD PTR [edi+620], eax
	mov eax, 0
	mov DWORD PTR [edi+624], eax
	mov eax, 0
	mov DWORD PTR [edi+628], eax
	mov eax, 0
	mov DWORD PTR [edi+632], eax
	mov eax, 0
	mov DWORD PTR [edi+636], eax
	mov eax, 0
	mov DWORD PTR [edi+640], eax
	mov eax, 0
	mov DWORD PTR [edi+644], eax
	mov eax, 0
	mov DWORD PTR [edi+648], eax
	mov eax, 0
	mov DWORD PTR [edi+652], eax
	mov eax, 0
	mov DWORD PTR [edi+656], eax
	mov eax, 0
	mov DWORD PTR [edi+660], eax
	mov eax, 239915481
	mov DWORD PTR [edi+664], eax
	mov eax, 53210446
	mov DWORD PTR [edi+668], eax
	mov eax, -2022960169
	mov DWORD PTR [edi+672], eax
	mov eax, -1335015917
	mov DWORD PTR [edi+676], eax
	mov eax, 151777808
	mov DWORD PTR [edi+680], eax
	mov eax, 108015705
	mov DWORD PTR [edi+684], eax
	mov eax, 771628954
	mov DWORD PTR [edi+688], eax
	mov eax, 516130721
	mov DWORD PTR [edi+692], eax
	mov eax, -918310840
	mov DWORD PTR [edi+696], eax
	mov eax, 748796127
	mov DWORD PTR [edi+700], eax
	mov eax, 0
	mov DWORD PTR [edi+704], eax
	mov eax, 0
	mov DWORD PTR [edi+708], eax
	mov eax, 0
	mov DWORD PTR [edi+712], eax
	mov eax, 0
	mov DWORD PTR [edi+716], eax
	mov eax, 0
	mov DWORD PTR [edi+720], eax
	mov eax, 0
	mov DWORD PTR [edi+724], eax
	mov eax, 0
	mov DWORD PTR [edi+728], eax
	mov eax, 0
	mov DWORD PTR [edi+732], eax
	mov eax, 0
	mov DWORD PTR [edi+736], eax
	mov eax, 0
	mov DWORD PTR [edi+740], eax
	mov eax, -1
	mov DWORD PTR [edi+1824], eax
	mov esi, 40
20:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+1304]
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
	mov esi, 40
21:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+544]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4420], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4421], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4422], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4423], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4424], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4425], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4426], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4427], dl
	test esi, esi
	jne 21b
	mov esi, 40
22:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+584]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4744], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4745], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4746], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4747], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4748], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4749], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4750], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4751], dl
	test esi, esi
	jne 22b
	mov eax, 1550791936
	mov DWORD PTR [edi+1664], eax
	mov eax, 1642259846
	mov DWORD PTR [edi+1668], eax
	mov eax, 1885706431
	mov DWORD PTR [edi+1672], eax
	mov eax, -1626685503
	mov DWORD PTR [edi+1676], eax
	mov eax, -718237428
	mov DWORD PTR [edi+1680], eax
	mov eax, 1441072705
	mov DWORD PTR [edi+1684], eax
	mov eax, -1009565093
	mov DWORD PTR [edi+1688], eax
	mov eax, -235477864
	mov DWORD PTR [edi+1692], eax
	mov eax, 253778633
	mov DWORD PTR [edi+1696], eax
	mov eax, 317161758
	mov DWORD PTR [edi+1700], eax
	mov eax, 144070016
	mov DWORD PTR [edi+624], eax
	mov eax, 1302438063
	mov DWORD PTR [edi+628], eax
	mov eax, 1699442841
	mov DWORD PTR [edi+632], eax
	mov eax, 1682373084
	mov DWORD PTR [edi+636], eax
	mov eax, 1912631511
	mov DWORD PTR [edi+640], eax
	mov eax, -1315401018
	mov DWORD PTR [edi+644], eax
	mov eax, -859946246
	mov DWORD PTR [edi+648], eax
	mov eax, -537810709
	mov DWORD PTR [edi+652], eax
	mov eax, -1779426282
	mov DWORD PTR [edi+656], eax
	mov eax, 1154850929
	mov DWORD PTR [edi+660], eax
	mov eax, -181842157
	mov DWORD PTR [edi+664], eax
	mov eax, 1012756772
	mov DWORD PTR [edi+668], eax
	mov eax, 2069068362
	mov DWORD PTR [edi+672], eax
	mov eax, 910603102
	mov DWORD PTR [edi+676], eax
	mov eax, -602258729
	mov DWORD PTR [edi+680], eax
	mov eax, -1936946579
	mov DWORD PTR [edi+684], eax
	mov eax, 141285537
	mov DWORD PTR [edi+688], eax
	mov eax, -1939820630
	mov DWORD PTR [edi+692], eax
	mov eax, 2092784966
	mov DWORD PTR [edi+696], eax
	mov eax, -1254900790
	mov DWORD PTR [edi+700], eax
	mov eax, 239915481
	mov DWORD PTR [edi+704], eax
	mov eax, 53210446
	mov DWORD PTR [edi+708], eax
	mov eax, -2022960169
	mov DWORD PTR [edi+712], eax
	mov eax, -1335015917
	mov DWORD PTR [edi+716], eax
	mov eax, 151777808
	mov DWORD PTR [edi+720], eax
	mov eax, 108015705
	mov DWORD PTR [edi+724], eax
	mov eax, 771628954
	mov DWORD PTR [edi+728], eax
	mov eax, 516130721
	mov DWORD PTR [edi+732], eax
	mov eax, -918310840
	mov DWORD PTR [edi+736], eax
	mov eax, 748796127
	mov DWORD PTR [edi+740], eax
	mov esi, 46
23:
	sub esi, 1
	cmp esi, 45
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
25:
	mov eax, esi
	mov ecx, 5120
	mul ecx
	mov edx, DWORD PTR [edi+60]
	add edx, eax
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
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
	mov ecx, 2
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+80]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+96]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+112]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+128]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+144]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 3
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+160]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+176]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+192]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+208]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+224]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 4
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+240]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+256]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+272]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+288]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+304]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 5
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
	movdqu xmm6, XMMWORD PTR [edx+384]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 6
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+400]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+416]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+432]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+448]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+464]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 7
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
	mov ecx, 8
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+560]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+576]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+592]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+608]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+624]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 9
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
	movdqu xmm6, XMMWORD PTR [edx+704]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 10
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+720]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+736]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+752]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+768]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+784]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 11
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+800]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+816]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+832]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+848]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+864]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 12
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+880]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+896]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+912]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+928]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+944]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 13
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
	mov ecx, 14
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1040]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1056]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1072]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1088]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1104]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 15
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1120]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1136]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1152]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1168]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1184]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 16
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1200]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1216]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1232]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1248]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1264]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 17
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
	movdqu xmm6, XMMWORD PTR [edx+1344]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 18
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1360]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1376]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1392]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1408]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1424]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 19
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
	mov ecx, 20
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1520]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1536]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1552]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1568]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1584]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 21
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
	movdqu xmm6, XMMWORD PTR [edx+1664]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 22
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1680]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1696]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1712]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1728]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1744]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 23
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1760]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1776]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1792]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1808]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1824]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 24
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1840]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1856]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1872]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1888]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1904]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 25
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
	movdqu xmm6, XMMWORD PTR [edx+1984]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 26
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2000]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2016]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2032]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2048]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2064]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 27
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2080]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2096]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2112]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2128]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2144]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 28
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2160]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2176]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2192]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2208]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2224]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 29
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
	movdqu xmm6, XMMWORD PTR [edx+2304]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 30
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2320]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2336]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2352]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2368]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2384]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 31
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2400]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2416]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2432]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2448]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2464]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 32
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2480]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2496]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2512]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2528]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2544]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 33
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
	movdqu xmm6, XMMWORD PTR [edx+2624]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 34
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2640]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2656]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2672]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2688]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2704]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 35
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2720]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2736]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2752]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2768]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2784]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 36
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2800]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2816]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2832]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2848]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2864]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 37
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
	movdqu xmm6, XMMWORD PTR [edx+2944]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 38
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2960]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2976]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2992]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3008]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3024]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 39
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3040]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3056]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3072]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3088]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3104]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 40
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3120]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3136]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3152]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3168]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3184]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 41
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
	movdqu xmm6, XMMWORD PTR [edx+3264]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 42
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3280]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3296]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3312]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3328]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3344]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 43
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3360]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3376]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3392]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3408]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3424]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 44
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3440]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3456]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3472]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3488]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3504]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 45
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
	movdqu xmm6, XMMWORD PTR [edx+3584]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 46
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3600]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3616]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3632]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3648]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3664]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 47
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3680]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3696]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3712]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3728]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3744]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 48
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3760]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3776]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3792]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3808]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3824]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 49
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
	movdqu xmm6, XMMWORD PTR [edx+3904]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 50
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3920]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3936]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3952]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3968]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3984]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 51
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4000]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4016]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4032]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4048]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4064]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 52
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4080]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4096]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4112]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4128]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4144]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 53
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4160]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4176]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4192]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4208]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4224]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 54
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4240]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4256]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4272]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4288]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4304]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 55
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4320]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4336]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4352]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4368]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4384]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 56
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4400]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4416]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4432]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4448]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4464]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 57
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4480]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4496]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4512]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4528]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4544]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 58
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4560]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4576]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4592]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4608]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4624]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 59
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4640]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4656]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4672]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4688]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4704]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 60
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4720]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4736]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4752]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4768]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4784]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 61
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4800]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4816]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4832]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4848]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4864]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 62
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4880]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4896]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4912]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4928]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4944]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 63
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4960]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4976]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4992]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5008]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5024]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 64
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5040]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5056]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5072]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5088]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5104]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu XMMWORD PTR [edi+864], xmm0
	movdqu XMMWORD PTR [edi+880], xmm1
	movdqu XMMWORD PTR [edi+896], xmm2
	movdqu XMMWORD PTR [edi+912], xmm3
	movdqu XMMWORD PTR [edi+928], xmm4
	mov eax, 239915481
	mov DWORD PTR [edi+944], eax
	mov eax, 53210446
	mov DWORD PTR [edi+948], eax
	mov eax, -2022960169
	mov DWORD PTR [edi+952], eax
	mov eax, -1335015917
	mov DWORD PTR [edi+956], eax
	mov eax, 151777808
	mov DWORD PTR [edi+960], eax
	mov eax, 108015705
	mov DWORD PTR [edi+964], eax
	mov eax, 771628954
	mov DWORD PTR [edi+968], eax
	mov eax, 516130721
	mov DWORD PTR [edi+972], eax
	mov eax, -918310840
	mov DWORD PTR [edi+976], eax
	mov eax, 748796127
	mov DWORD PTR [edi+980], eax
	mov ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+904]
	mov edx, DWORD PTR [edi+944]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+904], eax
	mov eax, DWORD PTR [edi+908]
	mov edx, DWORD PTR [edi+948]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+908], eax
	mov eax, DWORD PTR [edi+912]
	mov edx, DWORD PTR [edi+952]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+912], eax
	mov eax, DWORD PTR [edi+916]
	mov edx, DWORD PTR [edi+956]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+916], eax
	mov eax, DWORD PTR [edi+920]
	mov edx, DWORD PTR [edi+960]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+920], eax
	mov eax, DWORD PTR [edi+924]
	mov edx, DWORD PTR [edi+964]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+924], eax
	mov eax, DWORD PTR [edi+928]
	mov edx, DWORD PTR [edi+968]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [edi+932]
	mov edx, DWORD PTR [edi+972]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [edi+936]
	mov edx, DWORD PTR [edi+976]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+936], eax
	mov eax, DWORD PTR [edi+940]
	mov edx, DWORD PTR [edi+980]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+940], eax
	mov eax, DWORD PTR [edi+944]
	mov edx, DWORD PTR [edi+184]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+944], eax
	mov eax, DWORD PTR [edi+948]
	mov edx, DWORD PTR [edi+188]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+948], eax
	mov eax, DWORD PTR [edi+952]
	mov edx, DWORD PTR [edi+192]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+952], eax
	mov eax, DWORD PTR [edi+956]
	mov edx, DWORD PTR [edi+196]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+956], eax
	mov eax, DWORD PTR [edi+960]
	mov edx, DWORD PTR [edi+200]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+960], eax
	mov eax, DWORD PTR [edi+964]
	mov edx, DWORD PTR [edi+204]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+964], eax
	mov eax, DWORD PTR [edi+968]
	mov edx, DWORD PTR [edi+208]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+968], eax
	mov eax, DWORD PTR [edi+972]
	mov edx, DWORD PTR [edi+212]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+972], eax
	mov eax, DWORD PTR [edi+976]
	mov edx, DWORD PTR [edi+216]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+980]
	mov edx, DWORD PTR [edi+220]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+980], eax
	mov eax, 904
	mov ecx, 184
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	cmp esi, 45
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
	mov eax, DWORD PTR [edi+904]
	mov edx, DWORD PTR [edi+1264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+904], eax
	mov eax, DWORD PTR [edi+908]
	mov edx, DWORD PTR [edi+1268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+908], eax
	mov eax, DWORD PTR [edi+912]
	mov edx, DWORD PTR [edi+1272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+912], eax
	mov eax, DWORD PTR [edi+916]
	mov edx, DWORD PTR [edi+1276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+916], eax
	mov eax, DWORD PTR [edi+920]
	mov edx, DWORD PTR [edi+1280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+920], eax
	mov eax, DWORD PTR [edi+924]
	mov edx, DWORD PTR [edi+1284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+924], eax
	mov eax, DWORD PTR [edi+928]
	mov edx, DWORD PTR [edi+1288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [edi+932]
	mov edx, DWORD PTR [edi+1292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [edi+936]
	mov edx, DWORD PTR [edi+1296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+936], eax
	mov eax, DWORD PTR [edi+940]
	mov edx, DWORD PTR [edi+1300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+940], eax
	mov eax, 864
	mov ecx, 624
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 904
	mov ecx, 664
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 704
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 624
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 904
	mov ecx, 864
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 984
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 624
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 864
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1184
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 984
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1184
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 664
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 904
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 744
	mov ecx, 1184
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1024
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 744
	mov ecx, 1184
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 304
	mov edx, 824
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1664
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 744
	mov edx, 824
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 1024
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 1024
	mov edx, 824
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 744
	mov edx, 784
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 984
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 1024
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 304
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1664
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1024
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 984
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 304
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1024
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 784
	mov edx, 784
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1184
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 744
	mov ecx, 1104
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 744
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 1104
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 1184
	mov edx, 824
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 824
	mov edx, 824
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [edi+636], eax
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
	mov eax, DWORD PTR [edi+784]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+788]
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [edi+792]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+796]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+800]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+804]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+808]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+812]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+816]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+820]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [edi+824]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+828]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+832]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+836]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [edi+856]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+860]
	mov DWORD PTR [edi+740], eax
	test esi, esi
	jne 23b
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+1260], eax
	mov esi, 320
28:
	sub esi, 1
	mov eax, 1224
	mov ecx, 1224
	mov edx, 1224
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 1224
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4420]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1224]
	mov edx, DWORD PTR [edi+1264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+1228]
	mov edx, DWORD PTR [edi+1268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+1232]
	mov edx, DWORD PTR [edi+1272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+1236]
	mov edx, DWORD PTR [edi+1276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+1240]
	mov edx, DWORD PTR [edi+1280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+1244]
	mov edx, DWORD PTR [edi+1284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [edi+1248]
	mov edx, DWORD PTR [edi+1288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+1252]
	mov edx, DWORD PTR [edi+1292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+1256]
	mov edx, DWORD PTR [edi+1296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+1260]
	mov edx, DWORD PTR [edi+1300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1260], eax
	test esi, esi
	jne 28b
	mov eax, 1224
	mov ecx, 624
	mov edx, 1424
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 224
	mov ecx, 1424
	mov edx, 1464
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 184
	mov ecx, 1464
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 464
	mov ecx, 1304
	mov edx, 1544
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1344]
	sub edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+1348]
	sbb edx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+1352]
	sbb edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+1356]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+1360]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+1364]
	sbb edx, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+1368]
	sbb edx, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+1372]
	sbb edx, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+1376]
	sbb edx, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+1380]
	sbb edx, DWORD PTR [edi+140]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+1344]
	or edx, DWORD PTR [edi+1348]
	or edx, DWORD PTR [edi+1352]
	or edx, DWORD PTR [edi+1356]
	or edx, DWORD PTR [edi+1360]
	or edx, DWORD PTR [edi+1364]
	or edx, DWORD PTR [edi+1368]
	or edx, DWORD PTR [edi+1372]
	or edx, DWORD PTR [edi+1376]
	or edx, DWORD PTR [edi+1380]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+1824]
	and eax, edx
	mov DWORD PTR [edi+1824], eax
	mov edx, DWORD PTR [edi+1304]
	sub edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+1308]
	sbb edx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+1312]
	sbb edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+1316]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+1320]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+1324]
	sbb edx, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+1328]
	sbb edx, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+1332]
	sbb edx, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+1336]
	sbb edx, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+1340]
	sbb edx, DWORD PTR [edi+140]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+1304]
	or edx, DWORD PTR [edi+1308]
	or edx, DWORD PTR [edi+1312]
	or edx, DWORD PTR [edi+1316]
	or edx, DWORD PTR [edi+1320]
	or edx, DWORD PTR [edi+1324]
	or edx, DWORD PTR [edi+1328]
	or edx, DWORD PTR [edi+1332]
	or edx, DWORD PTR [edi+1336]
	or edx, DWORD PTR [edi+1340]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+1824]
	and eax, edx
	mov DWORD PTR [edi+1824], eax
	mov edx, DWORD PTR [edi+1504]
	or edx, DWORD PTR [edi+1508]
	or edx, DWORD PTR [edi+1512]
	or edx, DWORD PTR [edi+1516]
	or edx, DWORD PTR [edi+1520]
	or edx, DWORD PTR [edi+1524]
	or edx, DWORD PTR [edi+1528]
	or edx, DWORD PTR [edi+1532]
	or edx, DWORD PTR [edi+1536]
	or edx, DWORD PTR [edi+1540]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+1824]
	and eax, edx
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+516]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+520]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+524]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [edi+1260], eax
	mov esi, 320
29:
	sub esi, 1
	mov eax, 1224
	mov ecx, 1224
	mov edx, 1224
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1544
	mov ecx, 1224
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4744]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1224]
	mov edx, DWORD PTR [edi+1264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+1228]
	mov edx, DWORD PTR [edi+1268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+1232]
	mov edx, DWORD PTR [edi+1272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+1236]
	mov edx, DWORD PTR [edi+1276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+1240]
	mov edx, DWORD PTR [edi+1280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+1244]
	mov edx, DWORD PTR [edi+1284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [edi+1248]
	mov edx, DWORD PTR [edi+1288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+1252]
	mov edx, DWORD PTR [edi+1292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+1256]
	mov edx, DWORD PTR [edi+1296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+1260]
	mov edx, DWORD PTR [edi+1300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1260], eax
	test esi, esi
	jne 29b
	mov eax, 464
	mov ecx, 1504
	mov edx, 1584
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 464
	mov ecx, 1344
	mov edx, 1624
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 464
	mov ecx, 1384
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1624
	mov ecx, 1584
	mov edx, 1704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1704
	mov edx, 1704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1704
	mov ecx, 1224
	mov edx, 1744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 224
	mov ecx, 1744
	mov edx, 1784
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1784]
	or edx, DWORD PTR [edi+1788]
	or edx, DWORD PTR [edi+1792]
	or edx, DWORD PTR [edi+1796]
	or edx, DWORD PTR [edi+1800]
	or edx, DWORD PTR [edi+1804]
	or edx, DWORD PTR [edi+1808]
	or edx, DWORD PTR [edi+1812]
	or edx, DWORD PTR [edi+1816]
	or edx, DWORD PTR [edi+1820]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+1824]
	and eax, edx
	mov DWORD PTR [edi+1824], eax
	mov ecx, DWORD PTR [edi+1824]
	mov ebx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+1504]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+36], eax
	mov eax, DWORD PTR [edi+1508]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+32], eax
	mov eax, DWORD PTR [edi+1512]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+28], eax
	mov eax, DWORD PTR [edi+1516]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+24], eax
	mov eax, DWORD PTR [edi+1520]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+20], eax
	mov eax, DWORD PTR [edi+1524]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+16], eax
	mov eax, DWORD PTR [edi+1528]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+12], eax
	mov eax, DWORD PTR [edi+1532]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [edi+1536]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [edi+1540]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [edi+1784]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+76], eax
	mov eax, DWORD PTR [edi+1788]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+72], eax
	mov eax, DWORD PTR [edi+1792]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+68], eax
	mov eax, DWORD PTR [edi+1796]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+64], eax
	mov eax, DWORD PTR [edi+1800]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [edi+1804]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+56], eax
	mov eax, DWORD PTR [edi+1808]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+52], eax
	mov eax, DWORD PTR [edi+1812]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+48], eax
	mov eax, DWORD PTR [edi+1816]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+44], eax
	mov eax, DWORD PTR [edi+1820]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+40], eax
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	ret
	.p2align 6
