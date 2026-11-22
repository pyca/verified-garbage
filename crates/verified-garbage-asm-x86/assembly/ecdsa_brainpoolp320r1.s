// The functions of `src/ecdsa_brainpoolp320r1.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp320r1_verify:
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
	cmp eax, 40
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
	movzx eax, BYTE PTR [ecx+32]
	mov BYTE PTR [esp+60], al
	movzx eax, BYTE PTR [ecx+33]
	mov BYTE PTR [esp+61], al
	movzx eax, BYTE PTR [ecx+34]
	mov BYTE PTR [esp+62], al
	movzx eax, BYTE PTR [ecx+35]
	mov BYTE PTR [esp+63], al
	movzx eax, BYTE PTR [ecx+36]
	mov BYTE PTR [esp+64], al
	movzx eax, BYTE PTR [ecx+37]
	mov BYTE PTR [esp+65], al
	movzx eax, BYTE PTR [ecx+38]
	mov BYTE PTR [esp+66], al
	movzx eax, BYTE PTR [ecx+39]
	mov BYTE PTR [esp+67], al
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
	add edx, 68
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
	cmp eax, 68
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
	.long {VG_BRAINPOOLP320R1_COMB}
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
	mov esi, 40
25:
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
	jne 25b
	mov esi, 40
26:
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
	jne 26b
	mov esi, 40
27:
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
	jne 27b
	mov ebx, DWORD PTR [esp+12]
	add ebx, 40
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1268], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1272], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1276], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1280], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1284], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1288], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1292], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1296], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1300], eax
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
	mov ebx, DWORD PTR [esp+4]
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
	mov ebx, DWORD PTR [esp+4]
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
	mov edx, DWORD PTR [edi+1264]
	sub edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+1268]
	sbb edx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+1272]
	sbb edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+1276]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+1280]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+1284]
	sbb edx, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+1288]
	sbb edx, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+1292]
	sbb edx, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+1296]
	sbb edx, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+1300]
	sbb edx, DWORD PTR [edi+140]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+1264]
	or edx, DWORD PTR [edi+1268]
	or edx, DWORD PTR [edi+1272]
	or edx, DWORD PTR [edi+1276]
	or edx, DWORD PTR [edi+1280]
	or edx, DWORD PTR [edi+1284]
	or edx, DWORD PTR [edi+1288]
	or edx, DWORD PTR [edi+1292]
	or edx, DWORD PTR [edi+1296]
	or edx, DWORD PTR [edi+1300]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+1824]
	and eax, edx
	mov DWORD PTR [edi+1824], eax
	mov eax, 464
	mov ecx, 1264
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
28:
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
	jne 28b
	mov eax, 464
	mov ecx, 1344
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
	mov eax, 464
	mov ecx, 1304
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
	mov eax, 1224
	mov ecx, 1664
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
	mov eax, 1224
	mov ecx, 1624
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
	mov ecx, 1704
	mov edx, 1424
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
	mov edx, 1464
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 40
29:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+1424]
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
	jne 29b
	call {vg_brainpoolp320r1_comb}
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [edi+1704], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [edi+1708], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [edi+1712], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [edi+1716], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [edi+1720], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [edi+1724], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [edi+1728], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [edi+1732], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [edi+1736], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [edi+1740], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [edi+1744], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [edi+1748], eax
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+1752], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+1756], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+1760], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+1764], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+1768], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+1772], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+1776], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+1780], eax
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+1544], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+1548], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+1552], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+1556], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+1560], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+1564], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [edi+1568], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [edi+1572], eax
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [edi+1576], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [edi+1580], eax
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
	mov esi, 40
210:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+1464]
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
	call {vg_brainpoolp320r1_window}
	mov eax, 624
	mov ecx, 1704
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
	mov eax, 664
	mov ecx, 1744
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
	mov eax, 704
	mov ecx, 1544
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
	mov eax, 1744
	mov ecx, 1704
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
	mov eax, 664
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
	mov eax, 1544
	mov ecx, 1704
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
	mov eax, 704
	mov ecx, 624
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
	mov eax, 1544
	mov ecx, 1744
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
	mov eax, 704
	mov ecx, 664
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
	mov ecx, 344
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
	mov ecx, 344
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
	jne 211b
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
	mov eax, 464
	mov ecx, 1464
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
	mov eax, 1624
	mov ecx, 1584
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+704]
	or edx, DWORD PTR [edi+708]
	or edx, DWORD PTR [edi+712]
	or edx, DWORD PTR [edi+716]
	or edx, DWORD PTR [edi+720]
	or edx, DWORD PTR [edi+724]
	or edx, DWORD PTR [edi+728]
	or edx, DWORD PTR [edi+732]
	or edx, DWORD PTR [edi+736]
	or edx, DWORD PTR [edi+740]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+1824]
	and eax, edx
	mov DWORD PTR [edi+1824], eax
	mov edx, DWORD PTR [edi+1664]
	or edx, DWORD PTR [edi+1668]
	or edx, DWORD PTR [edi+1672]
	or edx, DWORD PTR [edi+1676]
	or edx, DWORD PTR [edi+1680]
	or edx, DWORD PTR [edi+1684]
	or edx, DWORD PTR [edi+1688]
	or edx, DWORD PTR [edi+1692]
	or edx, DWORD PTR [edi+1696]
	or edx, DWORD PTR [edi+1700]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+1824]
	and eax, edx
	mov DWORD PTR [edi+1824], eax
	mov ecx, DWORD PTR [edi+1824]
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	lea esp, [esp+108]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-132]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	movdqu XMMWORD PTR [esp+112], xmm0
	mov DWORD PTR [esp+128], ecx
	lea esp, [esp+132]
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

vg_ecdsa_brainpoolp320r1_sign:
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
	sub ecx, 40
	sbb edx, edx
	and ecx, edx
	add ecx, 40
	mov ebx, esp
	add ebx, 272
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
	mov eax, DWORD PTR [esi+36]
	bswap eax
	mov DWORD PTR [esp+196], eax
	sub eax, 1153798929
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esi+32]
	bswap eax
	mov DWORD PTR [esp+192], eax
	sbb eax, -2037295781
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esi+28]
	bswap eax
	mov DWORD PTR [esp+188], eax
	sbb eax, -293185303
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esi+24]
	bswap eax
	mov DWORD PTR [esp+184], eax
	sbb eax, 759705287
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esi+20]
	bswap eax
	mov DWORD PTR [esp+180], eax
	sbb eax, -1232137565
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esi+16]
	bswap eax
	mov DWORD PTR [esp+176], eax
	sbb eax, -108015707
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [esp+172], eax
	sbb eax, -771628955
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [esp+168], eax
	sbb eax, -516130722
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [esp+164], eax
	sbb eax, 918310839
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [esp+160], eax
	sbb eax, -748796128
	mov DWORD PTR [esp], eax
	sbb edx, edx
	mov eax, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+36]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+196], eax
	mov eax, DWORD PTR [esp+192]
	mov ecx, DWORD PTR [esp+32]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+192], eax
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
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+3825], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+3829], eax
	mov eax, DWORD PTR [esp+160]
	mov DWORD PTR [edi+3833], eax
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [edi+3837], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [edi+3841], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [edi+3845], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [edi+3849], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [edi+3853], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [edi+3857], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [edi+3861], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [edi+3865], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+3869], eax
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
	mov ecx, 81
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
	add eax, 81
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
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+3825], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+3829], eax
	mov eax, DWORD PTR [esp+160]
	mov DWORD PTR [edi+3833], eax
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [edi+3837], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [edi+3841], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [edi+3845], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [edi+3849], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [edi+3853], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [edi+3857], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [edi+3861], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [edi+3865], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+3869], eax
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
	mov ecx, 81
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
	add eax, 81
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
	cmp eax, 40
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
	call {vg_ecdsa_brainpoolp320r1_sign_k}
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
