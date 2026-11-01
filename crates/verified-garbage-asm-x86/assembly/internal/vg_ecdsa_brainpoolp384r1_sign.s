// The functions of `src/internal/vg_ecdsa_brainpoolp384r1_sign.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp384r1_sign:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+16]
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+1552], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+1556], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1560], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1564], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1568], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1572], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1576], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1580], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1584], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1588], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1592], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1596], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+1600], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+1604], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1608], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1612], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1616], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1620], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1624], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1628], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1632], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1636], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1640], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1644], eax
	mov ebx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+1648], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+1652], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1656], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1660], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1664], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1668], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1672], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1676], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1680], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1684], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1688], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1692], eax
	mov eax, 822602835
	mov DWORD PTR [edi+64], eax
	mov eax, -2025390061
	mov DWORD PTR [edi+68], eax
	mov eax, -1877140879
	mov DWORD PTR [edi+72], eax
	mov eax, -1395415255
	mov DWORD PTR [edi+76], eax
	mov eax, 2142703907
	mov DWORD PTR [edi+80], eax
	mov eax, 313645593
	mov DWORD PTR [edi+84], eax
	mov eax, -313239884
	mov DWORD PTR [edi+88], eax
	mov eax, 355430665
	mov DWORD PTR [edi+92], eax
	mov eax, 1357267423
	mov DWORD PTR [edi+96], eax
	mov eax, 257781630
	mov DWORD PTR [edi+100], eax
	mov eax, -1556583128
	mov DWORD PTR [edi+104], eax
	mov eax, -1934025086
	mov DWORD PTR [edi+108], eax
	mov eax, -385587867
	mov DWORD PTR [edi+112], eax
	mov eax, 998781442
	mov DWORD PTR [edi+116], eax
	mov eax, 1803535120
	mov DWORD PTR [edi+120], eax
	mov eax, -818235729
	mov DWORD PTR [edi+124], eax
	mov eax, -1409014361
	mov DWORD PTR [edi+128], eax
	mov eax, 521563756
	mov DWORD PTR [edi+132], eax
	mov eax, -313239885
	mov DWORD PTR [edi+136], eax
	mov eax, 355430665
	mov DWORD PTR [edi+140], eax
	mov eax, 1357267423
	mov DWORD PTR [edi+144], eax
	mov eax, 257781630
	mov DWORD PTR [edi+148], eax
	mov eax, -1556583128
	mov DWORD PTR [edi+152], eax
	mov eax, -1934025086
	mov DWORD PTR [edi+156], eax
	mov eax, 0
	mov DWORD PTR [edi+208], eax
	mov eax, 0
	mov DWORD PTR [edi+212], eax
	mov eax, 0
	mov DWORD PTR [edi+216], eax
	mov eax, 0
	mov DWORD PTR [edi+220], eax
	mov eax, 0
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
	mov eax, 1
	mov DWORD PTR [edi+256], eax
	mov eax, 0
	mov DWORD PTR [edi+260], eax
	mov eax, 0
	mov DWORD PTR [edi+264], eax
	mov eax, 0
	mov DWORD PTR [edi+268], eax
	mov eax, 0
	mov DWORD PTR [edi+272], eax
	mov eax, 0
	mov DWORD PTR [edi+276], eax
	mov eax, 0
	mov DWORD PTR [edi+280], eax
	mov eax, 0
	mov DWORD PTR [edi+284], eax
	mov eax, 0
	mov DWORD PTR [edi+288], eax
	mov eax, 0
	mov DWORD PTR [edi+292], eax
	mov eax, 0
	mov DWORD PTR [edi+296], eax
	mov eax, 0
	mov DWORD PTR [edi+300], eax
	mov eax, -822602835
	mov DWORD PTR [edi+304], eax
	mov eax, 2025390060
	mov DWORD PTR [edi+308], eax
	mov eax, 1877140878
	mov DWORD PTR [edi+312], eax
	mov eax, 1395415254
	mov DWORD PTR [edi+316], eax
	mov eax, -2142703908
	mov DWORD PTR [edi+320], eax
	mov eax, -313645594
	mov DWORD PTR [edi+324], eax
	mov eax, 313239883
	mov DWORD PTR [edi+328], eax
	mov eax, -355430666
	mov DWORD PTR [edi+332], eax
	mov eax, -1357267424
	mov DWORD PTR [edi+336], eax
	mov eax, -257781631
	mov DWORD PTR [edi+340], eax
	mov eax, 1556583127
	mov DWORD PTR [edi+344], eax
	mov eax, 1934025085
	mov DWORD PTR [edi+348], eax
	mov eax, 1181498521
	mov DWORD PTR [edi+352], eax
	mov eax, -618219371
	mov DWORD PTR [edi+356], eax
	mov eax, -245911429
	mov DWORD PTR [edi+360], eax
	mov eax, 1977086974
	mov DWORD PTR [edi+364], eax
	mov eax, -672068172
	mov DWORD PTR [edi+368], eax
	mov eax, -1821937223
	mov DWORD PTR [edi+372], eax
	mov eax, 894604148
	mov DWORD PTR [edi+376], eax
	mov eax, -402658843
	mov DWORD PTR [edi+380], eax
	mov eax, 1118833760
	mov DWORD PTR [edi+384], eax
	mov eax, 1074434015
	mov DWORD PTR [edi+388], eax
	mov eax, -1561804591
	mov DWORD PTR [edi+392], eax
	mov eax, 2083749921
	mov DWORD PTR [edi+396], eax
	mov eax, -783108108
	mov DWORD PTR [edi+400], eax
	mov eax, -708118102
	mov DWORD PTR [edi+404], eax
	mov eax, -789506761
	mov DWORD PTR [edi+408], eax
	mov eax, -172408786
	mov DWORD PTR [edi+412], eax
	mov eax, 1705851754
	mov DWORD PTR [edi+416], eax
	mov eax, 1449863730
	mov DWORD PTR [edi+420], eax
	mov eax, 236168662
	mov DWORD PTR [edi+424], eax
	mov eax, 815019886
	mov DWORD PTR [edi+428], eax
	mov eax, 612445752
	mov DWORD PTR [edi+432], eax
	mov eax, 1916572679
	mov DWORD PTR [edi+436], eax
	mov eax, 362489558
	mov DWORD PTR [edi+440], eax
	mov eax, 1124093550
	mov DWORD PTR [edi+444], eax
	mov eax, -734463039
	mov DWORD PTR [edi+448], eax
	mov eax, -1584800021
	mov DWORD PTR [edi+452], eax
	mov eax, -710375745
	mov DWORD PTR [edi+456], eax
	mov eax, 1727824104
	mov DWORD PTR [edi+460], eax
	mov eax, -1658835165
	mov DWORD PTR [edi+464], eax
	mov eax, -1799128855
	mov DWORD PTR [edi+468], eax
	mov eax, -111402652
	mov DWORD PTR [edi+472], eax
	mov eax, 109782606
	mov DWORD PTR [edi+476], eax
	mov eax, -1160970087
	mov DWORD PTR [edi+480], eax
	mov eax, -1663234609
	mov DWORD PTR [edi+484], eax
	mov eax, -1997193279
	mov DWORD PTR [edi+488], eax
	mov eax, -2063567565
	mov DWORD PTR [edi+492], eax
	mov eax, 232865957
	mov DWORD PTR [edi+496], eax
	mov eax, -415714511
	mov DWORD PTR [edi+500], eax
	mov eax, -946245803
	mov DWORD PTR [edi+504], eax
	mov eax, -169815482
	mov DWORD PTR [edi+508], eax
	mov eax, -1895352324
	mov DWORD PTR [edi+512], eax
	mov eax, -125630045
	mov DWORD PTR [edi+516], eax
	mov eax, -713977321
	mov DWORD PTR [edi+520], eax
	mov eax, -1585402668
	mov DWORD PTR [edi+524], eax
	mov eax, 1327619510
	mov DWORD PTR [edi+528], eax
	mov eax, -971627162
	mov DWORD PTR [edi+532], eax
	mov eax, 1166633141
	mov DWORD PTR [edi+536], eax
	mov eax, 754229346
	mov DWORD PTR [edi+540], eax
	mov eax, -562619250
	mov DWORD PTR [edi+544], eax
	mov eax, -1404120158
	mov DWORD PTR [edi+548], eax
	mov eax, 791374702
	mov DWORD PTR [edi+552], eax
	mov eax, 925257248
	mov DWORD PTR [edi+556], eax
	mov eax, -1744672630
	mov DWORD PTR [edi+560], eax
	mov eax, 714243643
	mov DWORD PTR [edi+564], eax
	mov eax, 1389840639
	mov DWORD PTR [edi+568], eax
	mov eax, 1464497355
	mov DWORD PTR [edi+572], eax
	mov eax, 1695965147
	mov DWORD PTR [edi+576], eax
	mov eax, -1886884407
	mov DWORD PTR [edi+580], eax
	mov eax, 1632540610
	mov DWORD PTR [edi+584], eax
	mov eax, 216568858
	mov DWORD PTR [edi+588], eax
	mov eax, 385587867
	mov DWORD PTR [edi+592], eax
	mov eax, -998781443
	mov DWORD PTR [edi+596], eax
	mov eax, -1803535121
	mov DWORD PTR [edi+600], eax
	mov eax, 818235728
	mov DWORD PTR [edi+604], eax
	mov eax, 1409014360
	mov DWORD PTR [edi+608], eax
	mov eax, -521563757
	mov DWORD PTR [edi+612], eax
	mov eax, 313239884
	mov DWORD PTR [edi+616], eax
	mov eax, -355430666
	mov DWORD PTR [edi+620], eax
	mov eax, -1357267424
	mov DWORD PTR [edi+624], eax
	mov eax, -257781631
	mov DWORD PTR [edi+628], eax
	mov eax, 1556583127
	mov DWORD PTR [edi+632], eax
	mov eax, 1934025085
	mov DWORD PTR [edi+636], eax
	mov eax, 822602833
	mov DWORD PTR [edi+640], eax
	mov eax, -2025390061
	mov DWORD PTR [edi+644], eax
	mov eax, -1877140879
	mov DWORD PTR [edi+648], eax
	mov eax, -1395415255
	mov DWORD PTR [edi+652], eax
	mov eax, 2142703907
	mov DWORD PTR [edi+656], eax
	mov eax, 313645593
	mov DWORD PTR [edi+660], eax
	mov eax, -313239884
	mov DWORD PTR [edi+664], eax
	mov eax, 355430665
	mov DWORD PTR [edi+668], eax
	mov eax, 1357267423
	mov DWORD PTR [edi+672], eax
	mov eax, 257781630
	mov DWORD PTR [edi+676], eax
	mov eax, -1556583128
	mov DWORD PTR [edi+680], eax
	mov eax, -1934025086
	mov DWORD PTR [edi+684], eax
	mov eax, -385587869
	mov DWORD PTR [edi+688], eax
	mov eax, 998781442
	mov DWORD PTR [edi+692], eax
	mov eax, 1803535120
	mov DWORD PTR [edi+696], eax
	mov eax, -818235729
	mov DWORD PTR [edi+700], eax
	mov eax, -1409014361
	mov DWORD PTR [edi+704], eax
	mov eax, 521563756
	mov DWORD PTR [edi+708], eax
	mov eax, -313239885
	mov DWORD PTR [edi+712], eax
	mov eax, 355430665
	mov DWORD PTR [edi+716], eax
	mov eax, 1357267423
	mov DWORD PTR [edi+720], eax
	mov eax, 257781630
	mov DWORD PTR [edi+724], eax
	mov eax, -1556583128
	mov DWORD PTR [edi+728], eax
	mov eax, -1934025086
	mov DWORD PTR [edi+732], eax
	mov eax, 0
	mov DWORD PTR [edi+736], eax
	mov eax, 0
	mov DWORD PTR [edi+740], eax
	mov eax, 0
	mov DWORD PTR [edi+744], eax
	mov eax, 0
	mov DWORD PTR [edi+748], eax
	mov eax, 0
	mov DWORD PTR [edi+752], eax
	mov eax, 0
	mov DWORD PTR [edi+756], eax
	mov eax, 0
	mov DWORD PTR [edi+760], eax
	mov eax, 0
	mov DWORD PTR [edi+764], eax
	mov eax, 0
	mov DWORD PTR [edi+768], eax
	mov eax, 0
	mov DWORD PTR [edi+772], eax
	mov eax, 0
	mov DWORD PTR [edi+776], eax
	mov eax, 0
	mov DWORD PTR [edi+780], eax
	mov eax, -822602835
	mov DWORD PTR [edi+784], eax
	mov eax, 2025390060
	mov DWORD PTR [edi+788], eax
	mov eax, 1877140878
	mov DWORD PTR [edi+792], eax
	mov eax, 1395415254
	mov DWORD PTR [edi+796], eax
	mov eax, -2142703908
	mov DWORD PTR [edi+800], eax
	mov eax, -313645594
	mov DWORD PTR [edi+804], eax
	mov eax, 313239883
	mov DWORD PTR [edi+808], eax
	mov eax, -355430666
	mov DWORD PTR [edi+812], eax
	mov eax, -1357267424
	mov DWORD PTR [edi+816], eax
	mov eax, -257781631
	mov DWORD PTR [edi+820], eax
	mov eax, 1556583127
	mov DWORD PTR [edi+824], eax
	mov eax, 1934025085
	mov DWORD PTR [edi+828], eax
	mov eax, 0
	mov DWORD PTR [edi+832], eax
	mov eax, 0
	mov DWORD PTR [edi+836], eax
	mov eax, 0
	mov DWORD PTR [edi+840], eax
	mov eax, 0
	mov DWORD PTR [edi+844], eax
	mov eax, 0
	mov DWORD PTR [edi+848], eax
	mov eax, 0
	mov DWORD PTR [edi+852], eax
	mov eax, 0
	mov DWORD PTR [edi+856], eax
	mov eax, 0
	mov DWORD PTR [edi+860], eax
	mov eax, 0
	mov DWORD PTR [edi+864], eax
	mov eax, 0
	mov DWORD PTR [edi+868], eax
	mov eax, 0
	mov DWORD PTR [edi+872], eax
	mov eax, 0
	mov DWORD PTR [edi+876], eax
	mov eax, -1
	mov DWORD PTR [edi+2176], eax
	mov esi, 48
20:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+1552]
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
	mov esi, 48
21:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+640]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4484], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4485], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4486], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4487], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4488], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4489], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4490], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4491], dl
	test esi, esi
	jne 21b
	mov esi, 48
22:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+688]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4872], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4873], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4874], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4875], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4876], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4877], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4878], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4879], dl
	test esi, esi
	jne 22b
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+516]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+520]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+524]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3356], eax
	mov esi, 384
23:
	sub esi, 1
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [edi+2976], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [edi+2980], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [edi+2984], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [edi+2988], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [edi+2992], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [edi+2996], eax
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [edi+3000], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [edi+3004], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+3008], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+3012], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+3016], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+3020], eax
	mov eax, DWORD PTR [edi+784]
	mov DWORD PTR [edi+3024], eax
	mov eax, DWORD PTR [edi+788]
	mov DWORD PTR [edi+3028], eax
	mov eax, DWORD PTR [edi+792]
	mov DWORD PTR [edi+3032], eax
	mov eax, DWORD PTR [edi+796]
	mov DWORD PTR [edi+3036], eax
	mov eax, DWORD PTR [edi+800]
	mov DWORD PTR [edi+3040], eax
	mov eax, DWORD PTR [edi+804]
	mov DWORD PTR [edi+3044], eax
	mov eax, DWORD PTR [edi+808]
	mov DWORD PTR [edi+3048], eax
	mov eax, DWORD PTR [edi+812]
	mov DWORD PTR [edi+3052], eax
	mov eax, DWORD PTR [edi+816]
	mov DWORD PTR [edi+3056], eax
	mov eax, DWORD PTR [edi+820]
	mov DWORD PTR [edi+3060], eax
	mov eax, DWORD PTR [edi+824]
	mov DWORD PTR [edi+3064], eax
	mov eax, DWORD PTR [edi+828]
	mov DWORD PTR [edi+3068], eax
	mov eax, DWORD PTR [edi+832]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+836]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+856]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+860]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+864]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+868]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+3116], eax
	push edi
	call {vg_brainpoolp384r1_point_double}
	pop eax
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [edi+2832]
	mov DWORD PTR [edi+2976], eax
	mov eax, DWORD PTR [edi+2836]
	mov DWORD PTR [edi+2980], eax
	mov eax, DWORD PTR [edi+2840]
	mov DWORD PTR [edi+2984], eax
	mov eax, DWORD PTR [edi+2844]
	mov DWORD PTR [edi+2988], eax
	mov eax, DWORD PTR [edi+2848]
	mov DWORD PTR [edi+2992], eax
	mov eax, DWORD PTR [edi+2852]
	mov DWORD PTR [edi+2996], eax
	mov eax, DWORD PTR [edi+2856]
	mov DWORD PTR [edi+3000], eax
	mov eax, DWORD PTR [edi+2860]
	mov DWORD PTR [edi+3004], eax
	mov eax, DWORD PTR [edi+2864]
	mov DWORD PTR [edi+3008], eax
	mov eax, DWORD PTR [edi+2868]
	mov DWORD PTR [edi+3012], eax
	mov eax, DWORD PTR [edi+2872]
	mov DWORD PTR [edi+3016], eax
	mov eax, DWORD PTR [edi+2876]
	mov DWORD PTR [edi+3020], eax
	mov eax, DWORD PTR [edi+2880]
	mov DWORD PTR [edi+3024], eax
	mov eax, DWORD PTR [edi+2884]
	mov DWORD PTR [edi+3028], eax
	mov eax, DWORD PTR [edi+2888]
	mov DWORD PTR [edi+3032], eax
	mov eax, DWORD PTR [edi+2892]
	mov DWORD PTR [edi+3036], eax
	mov eax, DWORD PTR [edi+2896]
	mov DWORD PTR [edi+3040], eax
	mov eax, DWORD PTR [edi+2900]
	mov DWORD PTR [edi+3044], eax
	mov eax, DWORD PTR [edi+2904]
	mov DWORD PTR [edi+3048], eax
	mov eax, DWORD PTR [edi+2908]
	mov DWORD PTR [edi+3052], eax
	mov eax, DWORD PTR [edi+2912]
	mov DWORD PTR [edi+3056], eax
	mov eax, DWORD PTR [edi+2916]
	mov DWORD PTR [edi+3060], eax
	mov eax, DWORD PTR [edi+2920]
	mov DWORD PTR [edi+3064], eax
	mov eax, DWORD PTR [edi+2924]
	mov DWORD PTR [edi+3068], eax
	mov eax, DWORD PTR [edi+2928]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+2932]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+2936]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+2940]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+2944]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+2948]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+2952]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+2956]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+2960]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+2964]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+2968]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+2972]
	mov DWORD PTR [edi+3116], eax
	push edi
	call {vg_brainpoolp384r1_point_add}
	pop eax
	mov edi, DWORD PTR [esp+20]
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4096]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+2976]
	mov edx, DWORD PTR [edi+2832]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+2980]
	mov edx, DWORD PTR [edi+2836]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+2984]
	mov edx, DWORD PTR [edi+2840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+2988]
	mov edx, DWORD PTR [edi+2844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+2992]
	mov edx, DWORD PTR [edi+2848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+2996]
	mov edx, DWORD PTR [edi+2852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+3000]
	mov edx, DWORD PTR [edi+2856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+3004]
	mov edx, DWORD PTR [edi+2860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+3008]
	mov edx, DWORD PTR [edi+2864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+3012]
	mov edx, DWORD PTR [edi+2868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+3016]
	mov edx, DWORD PTR [edi+2872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+3020]
	mov edx, DWORD PTR [edi+2876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+3024]
	mov edx, DWORD PTR [edi+2880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+3028]
	mov edx, DWORD PTR [edi+2884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+3032]
	mov edx, DWORD PTR [edi+2888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+3036]
	mov edx, DWORD PTR [edi+2892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [edi+3040]
	mov edx, DWORD PTR [edi+2896]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [edi+3044]
	mov edx, DWORD PTR [edi+2900]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [edi+3048]
	mov edx, DWORD PTR [edi+2904]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [edi+3052]
	mov edx, DWORD PTR [edi+2908]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [edi+3056]
	mov edx, DWORD PTR [edi+2912]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [edi+3060]
	mov edx, DWORD PTR [edi+2916]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [edi+3064]
	mov edx, DWORD PTR [edi+2920]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [edi+3068]
	mov edx, DWORD PTR [edi+2924]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+828], eax
	mov eax, DWORD PTR [edi+3072]
	mov edx, DWORD PTR [edi+2928]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [edi+3076]
	mov edx, DWORD PTR [edi+2932]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [edi+3080]
	mov edx, DWORD PTR [edi+2936]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [edi+3084]
	mov edx, DWORD PTR [edi+2940]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+3088]
	mov edx, DWORD PTR [edi+2944]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+3092]
	mov edx, DWORD PTR [edi+2948]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+3096]
	mov edx, DWORD PTR [edi+2952]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [edi+3100]
	mov edx, DWORD PTR [edi+2956]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [edi+3104]
	mov edx, DWORD PTR [edi+2960]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [edi+3108]
	mov edx, DWORD PTR [edi+2964]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [edi+3112]
	mov edx, DWORD PTR [edi+2968]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [edi+3116]
	mov edx, DWORD PTR [edi+2972]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+876], eax
	test esi, esi
	jne 23b
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+1472], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+1476], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+1480], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+1484], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+1488], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+1492], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+1496], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+1500], eax
	mov esi, 384
24:
	sub esi, 1
	mov eax, 1456
	mov ecx, 1456
	mov edx, 1456
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 1456
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4484]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1456]
	mov edx, DWORD PTR [edi+1504]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+1460]
	mov edx, DWORD PTR [edi+1508]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+1464]
	mov edx, DWORD PTR [edi+1512]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+1468]
	mov edx, DWORD PTR [edi+1516]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1472]
	mov edx, DWORD PTR [edi+1520]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1472], eax
	mov eax, DWORD PTR [edi+1476]
	mov edx, DWORD PTR [edi+1524]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1476], eax
	mov eax, DWORD PTR [edi+1480]
	mov edx, DWORD PTR [edi+1528]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1480], eax
	mov eax, DWORD PTR [edi+1484]
	mov edx, DWORD PTR [edi+1532]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1484], eax
	mov eax, DWORD PTR [edi+1488]
	mov edx, DWORD PTR [edi+1536]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1488], eax
	mov eax, DWORD PTR [edi+1492]
	mov edx, DWORD PTR [edi+1540]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1492], eax
	mov eax, DWORD PTR [edi+1496]
	mov edx, DWORD PTR [edi+1544]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1496], eax
	mov eax, DWORD PTR [edi+1500]
	mov edx, DWORD PTR [edi+1548]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1500], eax
	test esi, esi
	jne 24b
	mov eax, 1456
	mov ecx, 736
	mov edx, 1696
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 256
	mov ecx, 1696
	mov edx, 1744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 208
	mov ecx, 1744
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 1552
	mov edx, 1840
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1600]
	sub edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+1604]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+1608]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+1612]
	sbb edx, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+1616]
	sbb edx, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+1620]
	sbb edx, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+1624]
	sbb edx, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+1628]
	sbb edx, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+1632]
	sbb edx, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+1636]
	sbb edx, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+1640]
	sbb edx, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+1644]
	sbb edx, DWORD PTR [edi+156]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+1600]
	or edx, DWORD PTR [edi+1604]
	or edx, DWORD PTR [edi+1608]
	or edx, DWORD PTR [edi+1612]
	or edx, DWORD PTR [edi+1616]
	or edx, DWORD PTR [edi+1620]
	or edx, DWORD PTR [edi+1624]
	or edx, DWORD PTR [edi+1628]
	or edx, DWORD PTR [edi+1632]
	or edx, DWORD PTR [edi+1636]
	or edx, DWORD PTR [edi+1640]
	or edx, DWORD PTR [edi+1644]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov edx, DWORD PTR [edi+1552]
	sub edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+1556]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+1560]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+1564]
	sbb edx, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+1568]
	sbb edx, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+1572]
	sbb edx, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+1576]
	sbb edx, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+1580]
	sbb edx, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+1584]
	sbb edx, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+1588]
	sbb edx, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+1592]
	sbb edx, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+1596]
	sbb edx, DWORD PTR [edi+156]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+1552]
	or edx, DWORD PTR [edi+1556]
	or edx, DWORD PTR [edi+1560]
	or edx, DWORD PTR [edi+1564]
	or edx, DWORD PTR [edi+1568]
	or edx, DWORD PTR [edi+1572]
	or edx, DWORD PTR [edi+1576]
	or edx, DWORD PTR [edi+1580]
	or edx, DWORD PTR [edi+1584]
	or edx, DWORD PTR [edi+1588]
	or edx, DWORD PTR [edi+1592]
	or edx, DWORD PTR [edi+1596]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov edx, DWORD PTR [edi+1792]
	or edx, DWORD PTR [edi+1796]
	or edx, DWORD PTR [edi+1800]
	or edx, DWORD PTR [edi+1804]
	or edx, DWORD PTR [edi+1808]
	or edx, DWORD PTR [edi+1812]
	or edx, DWORD PTR [edi+1816]
	or edx, DWORD PTR [edi+1820]
	or edx, DWORD PTR [edi+1824]
	or edx, DWORD PTR [edi+1828]
	or edx, DWORD PTR [edi+1832]
	or edx, DWORD PTR [edi+1836]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [edi+1472], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [edi+1476], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [edi+1480], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [edi+1484], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [edi+1488], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [edi+1492], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [edi+1496], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [edi+1500], eax
	mov esi, 384
25:
	sub esi, 1
	mov eax, 1456
	mov ecx, 1456
	mov edx, 1456
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1840
	mov ecx, 1456
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4872]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1456]
	mov edx, DWORD PTR [edi+1504]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+1460]
	mov edx, DWORD PTR [edi+1508]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+1464]
	mov edx, DWORD PTR [edi+1512]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+1468]
	mov edx, DWORD PTR [edi+1516]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1472]
	mov edx, DWORD PTR [edi+1520]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1472], eax
	mov eax, DWORD PTR [edi+1476]
	mov edx, DWORD PTR [edi+1524]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1476], eax
	mov eax, DWORD PTR [edi+1480]
	mov edx, DWORD PTR [edi+1528]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1480], eax
	mov eax, DWORD PTR [edi+1484]
	mov edx, DWORD PTR [edi+1532]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1484], eax
	mov eax, DWORD PTR [edi+1488]
	mov edx, DWORD PTR [edi+1536]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1488], eax
	mov eax, DWORD PTR [edi+1492]
	mov edx, DWORD PTR [edi+1540]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1492], eax
	mov eax, DWORD PTR [edi+1496]
	mov edx, DWORD PTR [edi+1544]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1496], eax
	mov eax, DWORD PTR [edi+1500]
	mov edx, DWORD PTR [edi+1548]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1500], eax
	test esi, esi
	jne 25b
	mov eax, 544
	mov ecx, 1792
	mov edx, 1888
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 1600
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 1648
	mov edx, 1984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1936
	mov ecx, 1888
	mov edx, 2032
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 2032
	mov edx, 2032
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2032
	mov ecx, 1456
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 256
	mov ecx, 2080
	mov edx, 2128
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+2128]
	or edx, DWORD PTR [edi+2132]
	or edx, DWORD PTR [edi+2136]
	or edx, DWORD PTR [edi+2140]
	or edx, DWORD PTR [edi+2144]
	or edx, DWORD PTR [edi+2148]
	or edx, DWORD PTR [edi+2152]
	or edx, DWORD PTR [edi+2156]
	or edx, DWORD PTR [edi+2160]
	or edx, DWORD PTR [edi+2164]
	or edx, DWORD PTR [edi+2168]
	or edx, DWORD PTR [edi+2172]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov ecx, DWORD PTR [edi+2176]
	mov ebx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+1792]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+44], eax
	mov eax, DWORD PTR [edi+1796]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+40], eax
	mov eax, DWORD PTR [edi+1800]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+36], eax
	mov eax, DWORD PTR [edi+1804]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+32], eax
	mov eax, DWORD PTR [edi+1808]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+28], eax
	mov eax, DWORD PTR [edi+1812]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+24], eax
	mov eax, DWORD PTR [edi+1816]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+20], eax
	mov eax, DWORD PTR [edi+1820]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+16], eax
	mov eax, DWORD PTR [edi+1824]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+12], eax
	mov eax, DWORD PTR [edi+1828]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [edi+1832]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [edi+1836]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [edi+2128]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+92], eax
	mov eax, DWORD PTR [edi+2132]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+88], eax
	mov eax, DWORD PTR [edi+2136]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+84], eax
	mov eax, DWORD PTR [edi+2140]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+80], eax
	mov eax, DWORD PTR [edi+2144]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+76], eax
	mov eax, DWORD PTR [edi+2148]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+72], eax
	mov eax, DWORD PTR [edi+2152]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+68], eax
	mov eax, DWORD PTR [edi+2156]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+64], eax
	mov eax, DWORD PTR [edi+2160]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [edi+2164]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+56], eax
	mov eax, DWORD PTR [edi+2168]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+52], eax
	mov eax, DWORD PTR [edi+2172]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+48], eax
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	ret
	.p2align 6
