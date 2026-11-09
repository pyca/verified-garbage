// The functions of `src/ecdsa_p384.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p384_verify:
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
	cmp eax, 48
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
	movzx eax, BYTE PTR [ecx+40]
	mov BYTE PTR [esp+68], al
	movzx eax, BYTE PTR [ecx+41]
	mov BYTE PTR [esp+69], al
	movzx eax, BYTE PTR [ecx+42]
	mov BYTE PTR [esp+70], al
	movzx eax, BYTE PTR [ecx+43]
	mov BYTE PTR [esp+71], al
	movzx eax, BYTE PTR [ecx+44]
	mov BYTE PTR [esp+72], al
	movzx eax, BYTE PTR [ecx+45]
	mov BYTE PTR [esp+73], al
	movzx eax, BYTE PTR [ecx+46]
	mov BYTE PTR [esp+74], al
	movzx eax, BYTE PTR [ecx+47]
	mov BYTE PTR [esp+75], al
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
	add edx, 76
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
	cmp eax, 76
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
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+12]
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
	mov ebx, DWORD PTR [esp+8]
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
	mov eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, 0
	mov DWORD PTR [edi+68], eax
	mov eax, 0
	mov DWORD PTR [edi+72], eax
	mov eax, -1
	mov DWORD PTR [edi+76], eax
	mov eax, -2
	mov DWORD PTR [edi+80], eax
	mov eax, -1
	mov DWORD PTR [edi+84], eax
	mov eax, -1
	mov DWORD PTR [edi+88], eax
	mov eax, -1
	mov DWORD PTR [edi+92], eax
	mov eax, -1
	mov DWORD PTR [edi+96], eax
	mov eax, -1
	mov DWORD PTR [edi+100], eax
	mov eax, -1
	mov DWORD PTR [edi+104], eax
	mov eax, -1
	mov DWORD PTR [edi+108], eax
	mov eax, -859494029
	mov DWORD PTR [edi+112], eax
	mov eax, -320071318
	mov DWORD PTR [edi+116], eax
	mov eax, 1219536762
	mov DWORD PTR [edi+120], eax
	mov eax, 1478102450
	mov DWORD PTR [edi+124], eax
	mov eax, -197710369
	mov DWORD PTR [edi+128], eax
	mov eax, -949793407
	mov DWORD PTR [edi+132], eax
	mov eax, -1
	mov DWORD PTR [edi+136], eax
	mov eax, -1
	mov DWORD PTR [edi+140], eax
	mov eax, -1
	mov DWORD PTR [edi+144], eax
	mov eax, -1
	mov DWORD PTR [edi+148], eax
	mov eax, -1
	mov DWORD PTR [edi+152], eax
	mov eax, -1
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
	mov eax, 1
	mov DWORD PTR [edi+304], eax
	mov eax, -1
	mov DWORD PTR [edi+308], eax
	mov eax, -1
	mov DWORD PTR [edi+312], eax
	mov eax, 0
	mov DWORD PTR [edi+316], eax
	mov eax, 1
	mov DWORD PTR [edi+320], eax
	mov eax, 0
	mov DWORD PTR [edi+324], eax
	mov eax, 0
	mov DWORD PTR [edi+328], eax
	mov eax, 0
	mov DWORD PTR [edi+332], eax
	mov eax, 0
	mov DWORD PTR [edi+336], eax
	mov eax, 0
	mov DWORD PTR [edi+340], eax
	mov eax, 0
	mov DWORD PTR [edi+344], eax
	mov eax, 0
	mov DWORD PTR [edi+348], eax
	mov eax, -4
	mov DWORD PTR [edi+352], eax
	mov eax, 3
	mov DWORD PTR [edi+356], eax
	mov eax, 0
	mov DWORD PTR [edi+360], eax
	mov eax, -4
	mov DWORD PTR [edi+364], eax
	mov eax, -5
	mov DWORD PTR [edi+368], eax
	mov eax, -1
	mov DWORD PTR [edi+372], eax
	mov eax, -1
	mov DWORD PTR [edi+376], eax
	mov eax, -1
	mov DWORD PTR [edi+380], eax
	mov eax, -1
	mov DWORD PTR [edi+384], eax
	mov eax, -1
	mov DWORD PTR [edi+388], eax
	mov eax, -1
	mov DWORD PTR [edi+392], eax
	mov eax, -1
	mov DWORD PTR [edi+396], eax
	mov eax, -675051162
	mov DWORD PTR [edi+400], eax
	mov eax, 406100306
	mov DWORD PTR [edi+404], eax
	mov eax, 1860475076
	mov DWORD PTR [edi+408], eax
	mov eax, -444790389
	mov DWORD PTR [edi+412], eax
	mov eax, 1264584334
	mov DWORD PTR [edi+416], eax
	mov eax, 1742102993
	mov DWORD PTR [edi+420], eax
	mov eax, -1111842649
	mov DWORD PTR [edi+424], eax
	mov eax, -1448746037
	mov DWORD PTR [edi+428], eax
	mov eax, 1560699326
	mov DWORD PTR [edi+432], eax
	mov eax, 578905564
	mov DWORD PTR [edi+436], eax
	mov eax, 552550381
	mov DWORD PTR [edi+440], eax
	mov eax, 1729639394
	mov DWORD PTR [edi+444], eax
	mov eax, 1237366056
	mov DWORD PTR [edi+448], eax
	mov eax, 1037071718
	mov DWORD PTR [edi+452], eax
	mov eax, -1596535240
	mov DWORD PTR [edi+456], eax
	mov eax, 551778530
	mov DWORD PTR [edi+460], eax
	mov eax, 1411075438
	mov DWORD PTR [edi+464], eax
	mov eax, -2019804420
	mov DWORD PTR [edi+468], eax
	mov eax, 1503858431
	mov DWORD PTR [edi+472], eax
	mov eax, 1683261060
	mov DWORD PTR [edi+476], eax
	mov eax, 1632558635
	mov DWORD PTR [edi+480], eax
	mov eax, -2127562973
	mov DWORD PTR [edi+484], eax
	mov eax, 698225939
	mov DWORD PTR [edi+488], eax
	mov eax, 1295691202
	mov DWORD PTR [edi+492], eax
	mov eax, 1258530046
	mov DWORD PTR [edi+496], eax
	mov eax, 587480493
	mov DWORD PTR [edi+500], eax
	mov eax, 2075437484
	mov DWORD PTR [edi+504], eax
	mov eax, -1581274945
	mov DWORD PTR [edi+508], eax
	mov eax, 780382288
	mov DWORD PTR [edi+512], eax
	mov eax, -1951537322
	mov DWORD PTR [edi+516], eax
	mov eax, 1760886745
	mov DWORD PTR [edi+520], eax
	mov eax, -960277991
	mov DWORD PTR [edi+524], eax
	mov eax, 963225664
	mov DWORD PTR [edi+528], eax
	mov eax, -578813402
	mov DWORD PTR [edi+532], eax
	mov eax, 1511376361
	mov DWORD PTR [edi+536], eax
	mov eax, 729328578
	mov DWORD PTR [edi+540], eax
	mov eax, 431229353
	mov DWORD PTR [edi+544], eax
	mov eax, 758225700
	mov DWORD PTR [edi+548], eax
	mov eax, -551902183
	mov DWORD PTR [edi+552], eax
	mov eax, -12746267
	mov DWORD PTR [edi+556], eax
	mov eax, -55039673
	mov DWORD PTR [edi+560], eax
	mov eax, -1136768966
	mov DWORD PTR [edi+564], eax
	mov eax, 1252728005
	mov DWORD PTR [edi+568], eax
	mov eax, -737326825
	mov DWORD PTR [edi+572], eax
	mov eax, 673605781
	mov DWORD PTR [edi+576], eax
	mov eax, 1068522362
	mov DWORD PTR [edi+580], eax
	mov eax, 725204769
	mov DWORD PTR [edi+584], eax
	mov eax, 210038273
	mov DWORD PTR [edi+588], eax
	mov eax, 859494029
	mov DWORD PTR [edi+592], eax
	mov eax, 320071317
	mov DWORD PTR [edi+596], eax
	mov eax, -1219536763
	mov DWORD PTR [edi+600], eax
	mov eax, -1478102451
	mov DWORD PTR [edi+604], eax
	mov eax, 197710368
	mov DWORD PTR [edi+608], eax
	mov eax, 949793406
	mov DWORD PTR [edi+612], eax
	mov eax, 0
	mov DWORD PTR [edi+616], eax
	mov eax, 0
	mov DWORD PTR [edi+620], eax
	mov eax, 0
	mov DWORD PTR [edi+624], eax
	mov eax, 0
	mov DWORD PTR [edi+628], eax
	mov eax, 0
	mov DWORD PTR [edi+632], eax
	mov eax, 0
	mov DWORD PTR [edi+636], eax
	mov eax, -3
	mov DWORD PTR [edi+640], eax
	mov eax, 0
	mov DWORD PTR [edi+644], eax
	mov eax, 0
	mov DWORD PTR [edi+648], eax
	mov eax, -1
	mov DWORD PTR [edi+652], eax
	mov eax, -2
	mov DWORD PTR [edi+656], eax
	mov eax, -1
	mov DWORD PTR [edi+660], eax
	mov eax, -1
	mov DWORD PTR [edi+664], eax
	mov eax, -1
	mov DWORD PTR [edi+668], eax
	mov eax, -1
	mov DWORD PTR [edi+672], eax
	mov eax, -1
	mov DWORD PTR [edi+676], eax
	mov eax, -1
	mov DWORD PTR [edi+680], eax
	mov eax, -1
	mov DWORD PTR [edi+684], eax
	mov eax, -859494031
	mov DWORD PTR [edi+688], eax
	mov eax, -320071318
	mov DWORD PTR [edi+692], eax
	mov eax, 1219536762
	mov DWORD PTR [edi+696], eax
	mov eax, 1478102450
	mov DWORD PTR [edi+700], eax
	mov eax, -197710369
	mov DWORD PTR [edi+704], eax
	mov eax, -949793407
	mov DWORD PTR [edi+708], eax
	mov eax, -1
	mov DWORD PTR [edi+712], eax
	mov eax, -1
	mov DWORD PTR [edi+716], eax
	mov eax, -1
	mov DWORD PTR [edi+720], eax
	mov eax, -1
	mov DWORD PTR [edi+724], eax
	mov eax, -1
	mov DWORD PTR [edi+728], eax
	mov eax, -1
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
	mov eax, 1
	mov DWORD PTR [edi+784], eax
	mov eax, -1
	mov DWORD PTR [edi+788], eax
	mov eax, -1
	mov DWORD PTR [edi+792], eax
	mov eax, 0
	mov DWORD PTR [edi+796], eax
	mov eax, 1
	mov DWORD PTR [edi+800], eax
	mov eax, 0
	mov DWORD PTR [edi+804], eax
	mov eax, 0
	mov DWORD PTR [edi+808], eax
	mov eax, 0
	mov DWORD PTR [edi+812], eax
	mov eax, 0
	mov DWORD PTR [edi+816], eax
	mov eax, 0
	mov DWORD PTR [edi+820], eax
	mov eax, 0
	mov DWORD PTR [edi+824], eax
	mov eax, 0
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
25:
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
	jne 25b
	mov esi, 48
26:
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
	jne 26b
	mov esi, 48
27:
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
	jne 27b
	mov ebx, DWORD PTR [esp+12]
	add ebx, 48
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+1504], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+1508], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1512], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1516], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1524], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1544], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1548], eax
	mov eax, 1
	mov DWORD PTR [edi+1936], eax
	mov eax, -2
	mov DWORD PTR [edi+1940], eax
	mov eax, 0
	mov DWORD PTR [edi+1944], eax
	mov eax, 2
	mov DWORD PTR [edi+1948], eax
	mov eax, 0
	mov DWORD PTR [edi+1952], eax
	mov eax, -2
	mov DWORD PTR [edi+1956], eax
	mov eax, 0
	mov DWORD PTR [edi+1960], eax
	mov eax, 2
	mov DWORD PTR [edi+1964], eax
	mov eax, 1
	mov DWORD PTR [edi+1968], eax
	mov eax, 0
	mov DWORD PTR [edi+1972], eax
	mov eax, 0
	mov DWORD PTR [edi+1976], eax
	mov eax, 0
	mov DWORD PTR [edi+1980], eax
	mov eax, -1656672820
	mov DWORD PTR [edi+1984], eax
	mov eax, 135366769
	mov DWORD PTR [edi+1988], eax
	mov eax, 2051814124
	mov DWORD PTR [edi+1992], eax
	mov eax, -148263464
	mov DWORD PTR [edi+1996], eax
	mov eax, 421528110
	mov DWORD PTR [edi+2000], eax
	mov eax, 2012356763
	mov DWORD PTR [edi+2004], eax
	mov eax, -1802269982
	mov DWORD PTR [edi+2008], eax
	mov eax, -482915346
	mov DWORD PTR [edi+2012], eax
	mov eax, 520233108
	mov DWORD PTR [edi+2016], eax
	mov eax, -1238687244
	mov DWORD PTR [edi+2020], eax
	mov eax, 1615839225
	mov DWORD PTR [edi+2024], eax
	mov eax, -855109301
	mov DWORD PTR [edi+2028], eax
	mov ebx, DWORD PTR [esp+4]
	add ebx, 1
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
	add ebx, 48
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+1792], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+1796], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1800], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1804], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1808], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1812], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1832], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1836], eax
	mov ebx, DWORD PTR [esp+4]
	movzx edx, BYTE PTR [ebx]
	xor edx, 4
	sub edx, 1
	sbb edx, edx
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov edx, DWORD PTR [edi+1648]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+1652]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+1656]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+1660]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+1664]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+1668]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+1672]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+1676]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+1680]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+1684]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+1688]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+1692]
	sbb edx, DWORD PTR [edi+108]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov edx, DWORD PTR [edi+1792]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+1796]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+1800]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+1804]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+1808]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+1812]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+1816]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+1820]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+1824]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+1828]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+1832]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+1836]
	sbb edx, DWORD PTR [edi+108]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov eax, 1936
	mov ecx, 1648
	mov edx, 1696
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1936
	mov ecx, 1792
	mov edx, 1744
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1744
	mov ecx, 1744
	mov edx, 1840
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1696
	mov ecx, 1696
	mov edx, 2032
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1696
	mov ecx, 2032
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1696
	mov ecx, 352
	mov edx, 2032
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2032
	mov ecx, 2080
	mov edx, 1888
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 1888
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2080
	mov ecx, 1840
	mov edx, 2032
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+2032]
	or edx, DWORD PTR [edi+2036]
	or edx, DWORD PTR [edi+2040]
	or edx, DWORD PTR [edi+2044]
	or edx, DWORD PTR [edi+2048]
	or edx, DWORD PTR [edi+2052]
	or edx, DWORD PTR [edi+2056]
	or edx, DWORD PTR [edi+2060]
	or edx, DWORD PTR [edi+2064]
	or edx, DWORD PTR [edi+2068]
	or edx, DWORD PTR [edi+2072]
	or edx, DWORD PTR [edi+2076]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov ecx, DWORD PTR [edi+2176]
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+1696]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1888], eax
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+1700]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1892], eax
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+1704]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1896], eax
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+1708]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1900], eax
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+1712]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1904], eax
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+1716]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1908], eax
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+1720]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1912], eax
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+1724]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1916], eax
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+1728]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1920], eax
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+1732]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1924], eax
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+1736]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1928], eax
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+1740]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1932], eax
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+1744]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2128], eax
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+1748]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2132], eax
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+1752]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2136], eax
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+1756]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2140], eax
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+1760]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2144], eax
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+1764]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2148], eax
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+1768]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2152], eax
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+1772]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2156], eax
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+1776]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2160], eax
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+1780]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2164], eax
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+1784]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2168], eax
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+1788]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2172], eax
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
	mov edx, DWORD PTR [edi+1504]
	sub edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+1508]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+1512]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+1516]
	sbb edx, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+1520]
	sbb edx, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+1524]
	sbb edx, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+1528]
	sbb edx, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+1532]
	sbb edx, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+1536]
	sbb edx, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+1540]
	sbb edx, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+1544]
	sbb edx, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+1548]
	sbb edx, DWORD PTR [edi+156]
	sbb eax, eax
	mov ebx, eax
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
	or edx, DWORD PTR [edi+1544]
	or edx, DWORD PTR [edi+1548]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov eax, 544
	mov ecx, 1504
	mov edx, 1840
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
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
28:
	sub esi, 1
	mov eax, 1456
	mov ecx, 1456
	mov edx, 1456
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_n}
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
	call {vg_p384_mul_mod_n}
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
	jne 28b
	mov eax, 544
	mov ecx, 1600
	mov edx, 1984
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 1552
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1456
	mov ecx, 1984
	mov edx, 2032
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1456
	mov ecx, 1936
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 256
	mov ecx, 2032
	mov edx, 1696
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 256
	mov ecx, 2080
	mov edx, 1744
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1696]
	mov DWORD PTR [edi+1552], eax
	mov eax, DWORD PTR [edi+1700]
	mov DWORD PTR [edi+1556], eax
	mov eax, DWORD PTR [edi+1704]
	mov DWORD PTR [edi+1560], eax
	mov eax, DWORD PTR [edi+1708]
	mov DWORD PTR [edi+1564], eax
	mov eax, DWORD PTR [edi+1712]
	mov DWORD PTR [edi+1568], eax
	mov eax, DWORD PTR [edi+1716]
	mov DWORD PTR [edi+1572], eax
	mov eax, DWORD PTR [edi+1720]
	mov DWORD PTR [edi+1576], eax
	mov eax, DWORD PTR [edi+1724]
	mov DWORD PTR [edi+1580], eax
	mov eax, DWORD PTR [edi+1728]
	mov DWORD PTR [edi+1584], eax
	mov eax, DWORD PTR [edi+1732]
	mov DWORD PTR [edi+1588], eax
	mov eax, DWORD PTR [edi+1736]
	mov DWORD PTR [edi+1592], eax
	mov eax, DWORD PTR [edi+1740]
	mov DWORD PTR [edi+1596], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [edi+516]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [edi+520]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [edi+524]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [edi+828], eax
	push edi
	call {vg_p384_mul}
	pop eax
	mov edi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [edi+2032], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [edi+2036], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [edi+2040], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [edi+2044], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [edi+2048], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [edi+2052], eax
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [edi+2056], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [edi+2060], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+2064], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+2068], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+2072], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+2076], eax
	mov eax, DWORD PTR [edi+784]
	mov DWORD PTR [edi+2080], eax
	mov eax, DWORD PTR [edi+788]
	mov DWORD PTR [edi+2084], eax
	mov eax, DWORD PTR [edi+792]
	mov DWORD PTR [edi+2088], eax
	mov eax, DWORD PTR [edi+796]
	mov DWORD PTR [edi+2092], eax
	mov eax, DWORD PTR [edi+800]
	mov DWORD PTR [edi+2096], eax
	mov eax, DWORD PTR [edi+804]
	mov DWORD PTR [edi+2100], eax
	mov eax, DWORD PTR [edi+808]
	mov DWORD PTR [edi+2104], eax
	mov eax, DWORD PTR [edi+812]
	mov DWORD PTR [edi+2108], eax
	mov eax, DWORD PTR [edi+816]
	mov DWORD PTR [edi+2112], eax
	mov eax, DWORD PTR [edi+820]
	mov DWORD PTR [edi+2116], eax
	mov eax, DWORD PTR [edi+824]
	mov DWORD PTR [edi+2120], eax
	mov eax, DWORD PTR [edi+828]
	mov DWORD PTR [edi+2124], eax
	mov eax, DWORD PTR [edi+832]
	mov DWORD PTR [edi+1840], eax
	mov eax, DWORD PTR [edi+836]
	mov DWORD PTR [edi+1844], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+1848], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+1852], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+1856], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+1860], eax
	mov eax, DWORD PTR [edi+856]
	mov DWORD PTR [edi+1864], eax
	mov eax, DWORD PTR [edi+860]
	mov DWORD PTR [edi+1868], eax
	mov eax, DWORD PTR [edi+864]
	mov DWORD PTR [edi+1872], eax
	mov eax, DWORD PTR [edi+868]
	mov DWORD PTR [edi+1876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+1880], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+1884], eax
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
	mov eax, 1
	mov DWORD PTR [edi+784], eax
	mov eax, -1
	mov DWORD PTR [edi+788], eax
	mov eax, -1
	mov DWORD PTR [edi+792], eax
	mov eax, 0
	mov DWORD PTR [edi+796], eax
	mov eax, 1
	mov DWORD PTR [edi+800], eax
	mov eax, 0
	mov DWORD PTR [edi+804], eax
	mov eax, 0
	mov DWORD PTR [edi+808], eax
	mov eax, 0
	mov DWORD PTR [edi+812], eax
	mov eax, 0
	mov DWORD PTR [edi+816], eax
	mov eax, 0
	mov DWORD PTR [edi+820], eax
	mov eax, 0
	mov DWORD PTR [edi+824], eax
	mov eax, 0
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
	mov eax, DWORD PTR [edi+1744]
	mov DWORD PTR [edi+1552], eax
	mov eax, DWORD PTR [edi+1748]
	mov DWORD PTR [edi+1556], eax
	mov eax, DWORD PTR [edi+1752]
	mov DWORD PTR [edi+1560], eax
	mov eax, DWORD PTR [edi+1756]
	mov DWORD PTR [edi+1564], eax
	mov eax, DWORD PTR [edi+1760]
	mov DWORD PTR [edi+1568], eax
	mov eax, DWORD PTR [edi+1764]
	mov DWORD PTR [edi+1572], eax
	mov eax, DWORD PTR [edi+1768]
	mov DWORD PTR [edi+1576], eax
	mov eax, DWORD PTR [edi+1772]
	mov DWORD PTR [edi+1580], eax
	mov eax, DWORD PTR [edi+1776]
	mov DWORD PTR [edi+1584], eax
	mov eax, DWORD PTR [edi+1780]
	mov DWORD PTR [edi+1588], eax
	mov eax, DWORD PTR [edi+1784]
	mov DWORD PTR [edi+1592], eax
	mov eax, DWORD PTR [edi+1788]
	mov DWORD PTR [edi+1596], eax
	mov eax, DWORD PTR [edi+1888]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+1892]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+1896]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+1900]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+1904]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+1908]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+1912]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+1916]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+1920]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+1924]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+1928]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+1932]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+2128]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+2132]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+2136]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+2140]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [edi+2144]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [edi+2148]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+828], eax
	push edi
	call {vg_p384_mul}
	pop eax
	mov edi, DWORD PTR [esp+16]
	mov eax, 736
	mov ecx, 2032
	mov edx, 1168
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 784
	mov ecx, 2080
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 1840
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2080
	mov ecx, 2032
	mov edx, 1312
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 784
	mov ecx, 736
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1312
	mov edx, 1312
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1168
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1312
	mov edx, 1312
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1840
	mov ecx, 2032
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 736
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1360
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1168
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1360
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1840
	mov ecx, 2080
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 784
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 880
	mov ecx, 1408
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1216
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 880
	mov ecx, 1408
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 352
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 400
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 880
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 1216
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 1216
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 880
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 1168
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 1216
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 352
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 400
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1216
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1168
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 352
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1360
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1216
	mov edx, 1168
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1408
	mov edx, 1168
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 880
	mov ecx, 1312
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 880
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1312
	mov edx, 1168
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 1408
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 976
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+880]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+884]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+888]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+892]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+896]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+900]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+904]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+908]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+912]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+916]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+920]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+924]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+928]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+932]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+936]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+940]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [edi+944]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [edi+948]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [edi+952]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [edi+956]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [edi+960]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [edi+964]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [edi+968]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [edi+972]
	mov DWORD PTR [edi+828], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+1000]
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [edi+1004]
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [edi+1008]
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [edi+1012]
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [edi+1016]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [edi+1020]
	mov DWORD PTR [edi+876], eax
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
29:
	sub esi, 1
	mov eax, 1456
	mov ecx, 1456
	mov edx, 1456
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
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
	call {vg_p384_mul_mod_p}
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
	jne 29b
	mov eax, 1456
	mov ecx, 736
	mov edx, 1696
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
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
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 1744
	mov edx, 1888
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1936
	mov ecx, 1888
	mov edx, 1984
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+832]
	or edx, DWORD PTR [edi+836]
	or edx, DWORD PTR [edi+840]
	or edx, DWORD PTR [edi+844]
	or edx, DWORD PTR [edi+848]
	or edx, DWORD PTR [edi+852]
	or edx, DWORD PTR [edi+856]
	or edx, DWORD PTR [edi+860]
	or edx, DWORD PTR [edi+864]
	or edx, DWORD PTR [edi+868]
	or edx, DWORD PTR [edi+872]
	or edx, DWORD PTR [edi+876]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov edx, DWORD PTR [edi+1984]
	or edx, DWORD PTR [edi+1988]
	or edx, DWORD PTR [edi+1992]
	or edx, DWORD PTR [edi+1996]
	or edx, DWORD PTR [edi+2000]
	or edx, DWORD PTR [edi+2004]
	or edx, DWORD PTR [edi+2008]
	or edx, DWORD PTR [edi+2012]
	or edx, DWORD PTR [edi+2016]
	or edx, DWORD PTR [edi+2020]
	or edx, DWORD PTR [edi+2024]
	or edx, DWORD PTR [edi+2028]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov ecx, DWORD PTR [edi+2176]
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	lea esp, [esp+108]
	ret
	.p2align 6

vg_ecdsa_p384_sign:
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
	sub ecx, 48
	sbb edx, edx
	and ecx, edx
	add ecx, 48
	mov ebx, esp
	add ebx, 280
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
	mov eax, DWORD PTR [esi+44]
	bswap eax
	mov DWORD PTR [esp+204], eax
	sub eax, -859494029
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esi+40]
	bswap eax
	mov DWORD PTR [esp+200], eax
	sbb eax, -320071318
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esi+36]
	bswap eax
	mov DWORD PTR [esp+196], eax
	sbb eax, 1219536762
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esi+32]
	bswap eax
	mov DWORD PTR [esp+192], eax
	sbb eax, 1478102450
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esi+28]
	bswap eax
	mov DWORD PTR [esp+188], eax
	sbb eax, -197710369
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esi+24]
	bswap eax
	mov DWORD PTR [esp+184], eax
	sbb eax, -949793407
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esi+20]
	bswap eax
	mov DWORD PTR [esp+180], eax
	sbb eax, -1
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esi+16]
	bswap eax
	mov DWORD PTR [esp+176], eax
	sbb eax, -1
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [esp+172], eax
	sbb eax, -1
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [esp+168], eax
	sbb eax, -1
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [esp+164], eax
	sbb eax, -1
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [esp+160], eax
	sbb eax, -1
	mov DWORD PTR [esp], eax
	sbb edx, edx
	mov eax, DWORD PTR [esp+204]
	mov ecx, DWORD PTR [esp+44]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+204], eax
	mov eax, DWORD PTR [esp+200]
	mov ecx, DWORD PTR [esp+40]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+200], eax
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
	mov BYTE PTR [edi+2256], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2257], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2261], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2265], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2269], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2273], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2277], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2281], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esp+160]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2349], eax
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
	add edx, 2256
	mov ecx, 97
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
	add eax, 97
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
	add ebx, 3072
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
	mov BYTE PTR [edi+2256], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2257], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2261], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2265], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2269], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2273], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2277], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2281], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esp+160]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2349], eax
	mov esi, DWORD PTR [esp+532]
	add esi, 3072
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
	add edx, 2256
	mov ecx, 97
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
	add eax, 97
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
	add ebx, 3072
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
	mov eax, 8
	mov DWORD PTR [esp+156], eax
24:
	mov eax, 0
	mov DWORD PTR [esp+152], eax
25:
	mov esi, DWORD PTR [esp+532]
	add esi, 3072
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
	cmp eax, 48
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
	call {vg_ecdsa_p384_sign_k}
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
	mov BYTE PTR [edi+2256], al
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
	add edx, 2256
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
	add ebx, 3072
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
	ret
	.p2align 6
