// The functions of `src/ec_brainpoolp320r1_compressed.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp320r1_compress_public_key:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+8]
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
	mov ebx, DWORD PTR [esp+8]
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
	mov eax, 1950044921
	mov DWORD PTR [edi+1624], eax
	mov eax, -1722881910
	mov DWORD PTR [edi+1628], eax
	mov eax, -1872135953
	mov DWORD PTR [edi+1632], eax
	mov eax, -1035498867
	mov DWORD PTR [edi+1636], eax
	mov eax, 818263670
	mov DWORD PTR [edi+1640], eax
	mov eax, 525109279
	mov DWORD PTR [edi+1644], eax
	mov eax, -434841902
	mov DWORD PTR [edi+1648], eax
	mov eax, 1414900068
	mov DWORD PTR [edi+1652], eax
	mov eax, 1814925906
	mov DWORD PTR [edi+1656], eax
	mov eax, -1571177910
	mov DWORD PTR [edi+1660], eax
	mov eax, -1074668774
	mov DWORD PTR [edi+1664], eax
	mov eax, -919709448
	mov DWORD PTR [edi+1668], eax
	mov eax, 545553157
	mov DWORD PTR [edi+1672], eax
	mov eax, 347782110
	mov DWORD PTR [edi+1676], eax
	mov eax, -1772253447
	mov DWORD PTR [edi+1680], eax
	mov eax, 408347098
	mov DWORD PTR [edi+1684], eax
	mov eax, 580714765
	mov DWORD PTR [edi+1688], eax
	mov eax, -1854235534
	mov DWORD PTR [edi+1692], eax
	mov eax, 696800104
	mov DWORD PTR [edi+1696], eax
	mov eax, -1825132598
	mov DWORD PTR [edi+1700], eax
	mov ebx, DWORD PTR [esp+8]
	add ebx, 1
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
	add ebx, 40
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1504], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1508], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1512], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1516], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1524], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov ebx, DWORD PTR [esp+8]
	movzx edx, BYTE PTR [ebx]
	xor edx, 4
	sub edx, 1
	sbb edx, edx
	mov eax, DWORD PTR [edi+1824]
	and eax, edx
	mov DWORD PTR [edi+1824], eax
	mov edx, DWORD PTR [edi+1384]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+1388]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+1392]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+1396]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+1400]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+1404]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+1408]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+1412]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+1416]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+1420]
	sbb edx, DWORD PTR [edi+100]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+1824]
	and eax, edx
	mov DWORD PTR [edi+1824], eax
	mov edx, DWORD PTR [edi+1504]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+1508]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+1512]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+1516]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+1520]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+1524]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+1528]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+1532]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+1536]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+1540]
	sbb edx, DWORD PTR [edi+100]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+1824]
	and eax, edx
	mov DWORD PTR [edi+1824], eax
	mov eax, 1624
	mov ecx, 1384
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
	mov eax, 1624
	mov ecx, 1504
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
	mov eax, 1464
	mov ecx, 1464
	mov edx, 1544
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1424
	mov ecx, 1424
	mov edx, 1704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1424
	mov ecx, 1704
	mov edx, 1744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1424
	mov ecx, 304
	mov edx, 1704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1704
	mov ecx, 1744
	mov edx, 1584
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1584
	mov edx, 1744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1744
	mov ecx, 1544
	mov edx, 1704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1704]
	or edx, DWORD PTR [edi+1708]
	or edx, DWORD PTR [edi+1712]
	or edx, DWORD PTR [edi+1716]
	or edx, DWORD PTR [edi+1720]
	or edx, DWORD PTR [edi+1724]
	or edx, DWORD PTR [edi+1728]
	or edx, DWORD PTR [edi+1732]
	or edx, DWORD PTR [edi+1736]
	or edx, DWORD PTR [edi+1740]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+1824]
	and eax, edx
	mov DWORD PTR [edi+1824], eax
	mov ecx, DWORD PTR [edi+1824]
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+1424]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1584], eax
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+1428]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1588], eax
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+1432]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1592], eax
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+1436]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1596], eax
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+1440]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1600], eax
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+1444]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1604], eax
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+1448]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1608], eax
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+1452]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1612], eax
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+1456]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1616], eax
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+1460]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1620], eax
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+1464]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1784], eax
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+1468]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1788], eax
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+1472]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1792], eax
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+1476]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1796], eax
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+1480]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1800], eax
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+1484]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1804], eax
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+1488]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1808], eax
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+1492]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1812], eax
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+1496]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+1500]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1820], eax
	mov ecx, DWORD PTR [edi+1824]
	mov ebx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+1504]
	and eax, 1
	or eax, 2
	and eax, ecx
	mov BYTE PTR [ebx], al
	mov eax, DWORD PTR [edi+1384]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+37], eax
	mov eax, DWORD PTR [edi+1388]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+33], eax
	mov eax, DWORD PTR [edi+1392]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+29], eax
	mov eax, DWORD PTR [edi+1396]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+25], eax
	mov eax, DWORD PTR [edi+1400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+21], eax
	mov eax, DWORD PTR [edi+1404]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+17], eax
	mov eax, DWORD PTR [edi+1408]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+13], eax
	mov eax, DWORD PTR [edi+1412]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+9], eax
	mov eax, DWORD PTR [edi+1416]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+5], eax
	mov eax, DWORD PTR [edi+1420]
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

vg_ec_brainpoolp320r1_decompress_public_key:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+8]
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
	mov ebx, DWORD PTR [esp+8]
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
	mov eax, 1950044921
	mov DWORD PTR [edi+1624], eax
	mov eax, -1722881910
	mov DWORD PTR [edi+1628], eax
	mov eax, -1872135953
	mov DWORD PTR [edi+1632], eax
	mov eax, -1035498867
	mov DWORD PTR [edi+1636], eax
	mov eax, 818263670
	mov DWORD PTR [edi+1640], eax
	mov eax, 525109279
	mov DWORD PTR [edi+1644], eax
	mov eax, -434841902
	mov DWORD PTR [edi+1648], eax
	mov eax, 1414900068
	mov DWORD PTR [edi+1652], eax
	mov eax, 1814925906
	mov DWORD PTR [edi+1656], eax
	mov eax, -1571177910
	mov DWORD PTR [edi+1660], eax
	mov eax, -1074668774
	mov DWORD PTR [edi+1664], eax
	mov eax, -919709448
	mov DWORD PTR [edi+1668], eax
	mov eax, 545553157
	mov DWORD PTR [edi+1672], eax
	mov eax, 347782110
	mov DWORD PTR [edi+1676], eax
	mov eax, -1772253447
	mov DWORD PTR [edi+1680], eax
	mov eax, 408347098
	mov DWORD PTR [edi+1684], eax
	mov eax, 580714765
	mov DWORD PTR [edi+1688], eax
	mov eax, -1854235534
	mov DWORD PTR [edi+1692], eax
	mov eax, 696800104
	mov DWORD PTR [edi+1696], eax
	mov eax, -1825132598
	mov DWORD PTR [edi+1700], eax
	mov ebx, DWORD PTR [esp+8]
	add ebx, 1
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
	mov ebx, DWORD PTR [esp+8]
	movzx edx, BYTE PTR [ebx]
	mov DWORD PTR [edi+1344], edx
	or edx, 1
	xor edx, 3
	sub edx, 1
	sbb edx, edx
	mov eax, DWORD PTR [edi+1824]
	and eax, edx
	mov DWORD PTR [edi+1824], eax
	mov edx, DWORD PTR [edi+1384]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+1388]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+1392]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+1396]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+1400]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+1404]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+1408]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+1412]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+1416]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+1420]
	sbb edx, DWORD PTR [edi+100]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+1824]
	and eax, edx
	mov DWORD PTR [edi+1824], eax
	mov eax, 1624
	mov ecx, 1384
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
	mov eax, 1424
	mov ecx, 1424
	mov edx, 1704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1424
	mov ecx, 1704
	mov edx, 1744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1424
	mov ecx, 304
	mov edx, 1704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1704
	mov ecx, 1744
	mov edx, 1584
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1584
	mov edx, 1744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1744]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+1748]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+1752]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [edi+1744]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [edi+1748]
	mov DWORD PTR [edi+1268], eax
	mov eax, DWORD PTR [edi+1752]
	mov DWORD PTR [edi+1272], eax
	mov eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+1276], eax
	mov eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+1280], eax
	mov eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+1284], eax
	mov eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+1288], eax
	mov eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+1292], eax
	mov eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+1296], eax
	mov eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+1300], eax
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+580], eax
	mov esi, 1
20:
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
	test esi, esi
	jne 20b
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1544], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1548], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1552], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1556], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1560], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1564], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1568], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1572], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1576], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1580], eax
	mov eax, 544
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
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+620], eax
	mov eax, 1544
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
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1020], eax
	mov eax, 1544
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
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1060], eax
	mov eax, 1544
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
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1100], eax
	mov eax, 1544
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
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1140], eax
	mov eax, 1544
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
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1180], eax
	mov eax, 1544
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
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1196], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1200], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1204], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1208], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1212], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1260], eax
	mov esi, 6
21:
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
	test esi, esi
	jne 21b
	mov eax, 1144
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
	mov esi, 4
22:
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
	test esi, esi
	jne 22b
	mov eax, 1024
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
	mov esi, 4
23:
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
	test esi, esi
	jne 23b
	mov eax, 1064
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
	mov esi, 5
24:
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
	test esi, esi
	jne 24b
	mov eax, 584
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
	mov esi, 4
25:
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
	test esi, esi
	jne 25b
	mov eax, 1064
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
	mov esi, 9
26:
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
	test esi, esi
	jne 26b
	mov eax, 584
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
	mov esi, 5
27:
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
	test esi, esi
	jne 27b
	mov eax, 1144
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
	mov esi, 5
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
	test esi, esi
	jne 28b
	mov eax, 1184
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
	mov esi, 4
29:
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
	test esi, esi
	jne 29b
	mov eax, 544
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
	mov esi, 5
210:
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
	test esi, esi
	jne 210b
	mov eax, 1024
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
	mov esi, 4
211:
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
	test esi, esi
	jne 211b
	mov eax, 1144
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
	mov esi, 4
212:
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
	test esi, esi
	jne 212b
	mov eax, 1104
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
	mov esi, 4
213:
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
	test esi, esi
	jne 213b
	mov eax, 1184
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
	mov esi, 5
214:
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
	test esi, esi
	jne 214b
	mov eax, 544
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
	mov esi, 6
215:
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
	test esi, esi
	jne 215b
	mov eax, 1184
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
	mov esi, 7
216:
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
	test esi, esi
	jne 216b
	mov eax, 1184
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
	mov esi, 5
217:
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
	test esi, esi
	jne 217b
	mov eax, 544
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
	mov esi, 4
218:
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
	test esi, esi
	jne 218b
	mov eax, 1024
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
	mov esi, 4
219:
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
	test esi, esi
	jne 219b
	mov eax, 1104
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
	mov esi, 5
220:
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
	test esi, esi
	jne 220b
	mov eax, 1064
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
	mov esi, 12
221:
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
	test esi, esi
	jne 221b
	mov eax, 1184
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
	mov esi, 8
222:
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
	test esi, esi
	jne 222b
	mov eax, 584
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
	mov esi, 6
223:
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
	test esi, esi
	jne 223b
	mov eax, 1104
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
	mov esi, 4
224:
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
	test esi, esi
	jne 224b
	mov eax, 1184
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
	mov esi, 4
225:
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
	test esi, esi
	jne 225b
	mov eax, 584
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
	mov esi, 4
226:
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
	test esi, esi
	jne 226b
	mov eax, 544
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
	mov esi, 4
227:
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
	test esi, esi
	jne 227b
	mov eax, 1184
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
	mov esi, 4
228:
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
	test esi, esi
	jne 228b
	mov eax, 1064
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
	mov esi, 4
229:
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
	test esi, esi
	jne 229b
	mov eax, 1184
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
	mov esi, 5
230:
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
	test esi, esi
	jne 230b
	mov eax, 1064
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
	mov esi, 4
231:
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
	test esi, esi
	jne 231b
	mov eax, 1104
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
	mov esi, 4
232:
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
	test esi, esi
	jne 232b
	mov eax, 1144
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
	mov esi, 4
233:
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
	test esi, esi
	jne 233b
	mov eax, 1104
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
	mov esi, 4
234:
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
	test esi, esi
	jne 234b
	mov eax, 1144
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
	mov esi, 8
235:
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
	test esi, esi
	jne 235b
	mov eax, 584
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
	mov esi, 4
236:
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
	test esi, esi
	jne 236b
	mov eax, 1024
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
	mov esi, 4
237:
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
	test esi, esi
	jne 237b
	mov eax, 1104
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
	mov esi, 4
238:
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
	test esi, esi
	jne 238b
	mov eax, 1144
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
	mov esi, 6
239:
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
	test esi, esi
	jne 239b
	mov eax, 1184
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
	mov esi, 4
240:
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
	test esi, esi
	jne 240b
	mov eax, 1064
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
	mov esi, 5
241:
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
	test esi, esi
	jne 241b
	mov eax, 984
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
	mov esi, 4
242:
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
	test esi, esi
	jne 242b
	mov eax, 1024
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
	mov esi, 5
243:
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
	test esi, esi
	jne 243b
	mov eax, 1024
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
	mov esi, 4
244:
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
	test esi, esi
	jne 244b
	mov eax, 1104
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
	mov esi, 7
245:
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
	test esi, esi
	jne 245b
	mov eax, 1184
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
	mov esi, 7
246:
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
	test esi, esi
	jne 246b
	mov eax, 1064
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
	mov esi, 6
247:
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
	test esi, esi
	jne 247b
	mov eax, 1184
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
	mov esi, 4
248:
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
	test esi, esi
	jne 248b
	mov eax, 1104
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
	mov esi, 7
249:
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
	test esi, esi
	jne 249b
	mov eax, 984
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
	mov esi, 5
250:
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
	test esi, esi
	jne 250b
	mov eax, 584
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
	mov esi, 4
251:
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
	test esi, esi
	jne 251b
	mov eax, 1184
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
	mov esi, 4
252:
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
	test esi, esi
	jne 252b
	mov eax, 584
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
	mov esi, 4
253:
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
	test esi, esi
	jne 253b
	mov eax, 984
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
	mov esi, 9
254:
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
	test esi, esi
	jne 254b
	mov eax, 1064
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
	mov esi, 5
255:
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
	test esi, esi
	jne 255b
	mov eax, 1104
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
	mov esi, 4
256:
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
	test esi, esi
	jne 256b
	mov eax, 544
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
	mov esi, 4
257:
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
	test esi, esi
	jne 257b
	mov eax, 1184
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
	mov esi, 7
258:
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
	test esi, esi
	jne 258b
	mov eax, 1144
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
	mov esi, 4
259:
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
	test esi, esi
	jne 259b
	mov eax, 1064
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
	mov esi, 4
260:
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
	test esi, esi
	jne 260b
	mov eax, 1064
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
	mov esi, 4
261:
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
	test esi, esi
	jne 261b
	mov eax, 1024
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
	mov esi, 6
262:
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
	test esi, esi
	jne 262b
	mov eax, 984
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
	mov esi, 1
263:
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
	test esi, esi
	jne 263b
	mov eax, 224
	mov ecx, 1224
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1504
	mov ecx, 184
	mov edx, 1544
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1504]
	mov ecx, DWORD PTR [edi+1344]
	xor ecx, eax
	and ecx, 1
	mov edx, 0
	sub edx, ecx
	mov ecx, edx
	mov eax, DWORD PTR [edi+1504]
	mov edx, DWORD PTR [edi+1544]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1504], eax
	mov eax, DWORD PTR [edi+1508]
	mov edx, DWORD PTR [edi+1548]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1508], eax
	mov eax, DWORD PTR [edi+1512]
	mov edx, DWORD PTR [edi+1552]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1512], eax
	mov eax, DWORD PTR [edi+1516]
	mov edx, DWORD PTR [edi+1556]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1516], eax
	mov eax, DWORD PTR [edi+1520]
	mov edx, DWORD PTR [edi+1560]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [edi+1524]
	mov edx, DWORD PTR [edi+1564]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1524], eax
	mov eax, DWORD PTR [edi+1528]
	mov edx, DWORD PTR [edi+1568]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1532]
	mov edx, DWORD PTR [edi+1572]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1536]
	mov edx, DWORD PTR [edi+1576]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1540]
	mov edx, DWORD PTR [edi+1580]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1540], eax
	mov eax, 1624
	mov ecx, 1504
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
	mov eax, 1464
	mov ecx, 1464
	mov edx, 1704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1744
	mov ecx, 1704
	mov edx, 1584
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1584]
	or edx, DWORD PTR [edi+1588]
	or edx, DWORD PTR [edi+1592]
	or edx, DWORD PTR [edi+1596]
	or edx, DWORD PTR [edi+1600]
	or edx, DWORD PTR [edi+1604]
	or edx, DWORD PTR [edi+1608]
	or edx, DWORD PTR [edi+1612]
	or edx, DWORD PTR [edi+1616]
	or edx, DWORD PTR [edi+1620]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+1824]
	and eax, edx
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [edi+1504]
	mov ecx, DWORD PTR [edi+1344]
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
	mov eax, DWORD PTR [edi+1824]
	and eax, edx
	mov DWORD PTR [edi+1824], eax
	mov ecx, DWORD PTR [edi+1824]
	mov ebx, DWORD PTR [esp+4]
	mov eax, 4
	and eax, ecx
	mov BYTE PTR [ebx], al
	mov eax, DWORD PTR [edi+1384]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+37], eax
	mov eax, DWORD PTR [edi+1388]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+33], eax
	mov eax, DWORD PTR [edi+1392]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+29], eax
	mov eax, DWORD PTR [edi+1396]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+25], eax
	mov eax, DWORD PTR [edi+1400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+21], eax
	mov eax, DWORD PTR [edi+1404]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+17], eax
	mov eax, DWORD PTR [edi+1408]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+13], eax
	mov eax, DWORD PTR [edi+1412]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+9], eax
	mov eax, DWORD PTR [edi+1416]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+5], eax
	mov eax, DWORD PTR [edi+1420]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+1], eax
	mov eax, DWORD PTR [edi+1504]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+77], eax
	mov eax, DWORD PTR [edi+1508]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+73], eax
	mov eax, DWORD PTR [edi+1512]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+69], eax
	mov eax, DWORD PTR [edi+1516]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+65], eax
	mov eax, DWORD PTR [edi+1520]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+61], eax
	mov eax, DWORD PTR [edi+1524]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+57], eax
	mov eax, DWORD PTR [edi+1528]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+53], eax
	mov eax, DWORD PTR [edi+1532]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+49], eax
	mov eax, DWORD PTR [edi+1536]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+45], eax
	mov eax, DWORD PTR [edi+1540]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+41], eax
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
