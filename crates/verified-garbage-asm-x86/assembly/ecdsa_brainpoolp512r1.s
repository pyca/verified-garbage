// The functions of `src/ecdsa_brainpoolp512r1.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp512r1_verify:
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
	cmp eax, 64
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
	movzx eax, BYTE PTR [ecx+48]
	mov BYTE PTR [esp+76], al
	movzx eax, BYTE PTR [ecx+49]
	mov BYTE PTR [esp+77], al
	movzx eax, BYTE PTR [ecx+50]
	mov BYTE PTR [esp+78], al
	movzx eax, BYTE PTR [ecx+51]
	mov BYTE PTR [esp+79], al
	movzx eax, BYTE PTR [ecx+52]
	mov BYTE PTR [esp+80], al
	movzx eax, BYTE PTR [ecx+53]
	mov BYTE PTR [esp+81], al
	movzx eax, BYTE PTR [ecx+54]
	mov BYTE PTR [esp+82], al
	movzx eax, BYTE PTR [ecx+55]
	mov BYTE PTR [esp+83], al
	movzx eax, BYTE PTR [ecx+56]
	mov BYTE PTR [esp+84], al
	movzx eax, BYTE PTR [ecx+57]
	mov BYTE PTR [esp+85], al
	movzx eax, BYTE PTR [ecx+58]
	mov BYTE PTR [esp+86], al
	movzx eax, BYTE PTR [ecx+59]
	mov BYTE PTR [esp+87], al
	movzx eax, BYTE PTR [ecx+60]
	mov BYTE PTR [esp+88], al
	movzx eax, BYTE PTR [ecx+61]
	mov BYTE PTR [esp+89], al
	movzx eax, BYTE PTR [ecx+62]
	mov BYTE PTR [esp+90], al
	movzx eax, BYTE PTR [ecx+63]
	mov BYTE PTR [esp+91], al
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
	add edx, 92
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
	cmp eax, 92
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
	.long {VG_BRAINPOOLP512R1_COMB}
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
	mov eax, DWORD PTR [ebx+60]
	bswap eax
	mov DWORD PTR [edi+2048], eax
	mov eax, DWORD PTR [ebx+56]
	bswap eax
	mov DWORD PTR [edi+2052], eax
	mov eax, DWORD PTR [ebx+52]
	bswap eax
	mov DWORD PTR [edi+2056], eax
	mov eax, DWORD PTR [ebx+48]
	bswap eax
	mov DWORD PTR [edi+2060], eax
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+2064], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+2068], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+2072], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+2076], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+2080], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+2084], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+2088], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+2092], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+2096], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+2100], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+2104], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+2108], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+60]
	bswap eax
	mov DWORD PTR [edi+2112], eax
	mov eax, DWORD PTR [ebx+56]
	bswap eax
	mov DWORD PTR [edi+2116], eax
	mov eax, DWORD PTR [ebx+52]
	bswap eax
	mov DWORD PTR [edi+2120], eax
	mov eax, DWORD PTR [ebx+48]
	bswap eax
	mov DWORD PTR [edi+2124], eax
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+2128], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+2132], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+2136], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+2140], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+2144], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+2148], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+2152], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+2156], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+2160], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+2164], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+2168], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+2172], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+60]
	bswap eax
	mov DWORD PTR [edi+2176], eax
	mov eax, DWORD PTR [ebx+56]
	bswap eax
	mov DWORD PTR [edi+2180], eax
	mov eax, DWORD PTR [ebx+52]
	bswap eax
	mov DWORD PTR [edi+2184], eax
	mov eax, DWORD PTR [ebx+48]
	bswap eax
	mov DWORD PTR [edi+2188], eax
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+2192], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+2196], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+2200], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+2204], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+2208], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+2212], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+2216], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+2220], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+2236], eax
	mov eax, 1480214771
	mov DWORD PTR [edi+64], eax
	mov eax, 682254422
	mov DWORD PTR [edi+68], eax
	mov eax, 763545221
	mov DWORD PTR [edi+72], eax
	mov eax, 679608111
	mov DWORD PTR [edi+76], eax
	mov eax, -425492250
	mov DWORD PTR [edi+80], eax
	mov eax, -1362255574
	mov DWORD PTR [edi+84], eax
	mov eax, -1681495998
	mov DWORD PTR [edi+88], eax
	mov eax, 2102237952
	mov DWORD PTR [edi+92], eax
	mov eax, 1882392689
	mov DWORD PTR [edi+96], eax
	mov eax, -698114870
	mov DWORD PTR [edi+100], eax
	mov eax, -1278619122
	mov DWORD PTR [edi+104], eax
	mov eax, -886010445
	mov DWORD PTR [edi+108], eax
	mov eax, 868875271
	mov DWORD PTR [edi+112], eax
	mov eax, 1070917294
	mov DWORD PTR [edi+116], eax
	mov eax, -605436789
	mov DWORD PTR [edi+120], eax
	mov eax, -1428316744
	mov DWORD PTR [edi+124], eax
	mov eax, -1666645911
	mov DWORD PTR [edi+128], eax
	mov eax, -1249405310
	mov DWORD PTR [edi+132], eax
	mov eax, 140368605
	mov DWORD PTR [edi+136], eax
	mov eax, 498193281
	mov DWORD PTR [edi+140], eax
	mov eax, 2141982791
	mov DWORD PTR [edi+144], eax
	mov eax, 1099325721
	mov DWORD PTR [edi+148], eax
	mov eax, 1286153753
	mov DWORD PTR [edi+152], eax
	mov eax, 1430150209
	mov DWORD PTR [edi+156], eax
	mov eax, 1882392688
	mov DWORD PTR [edi+160], eax
	mov eax, -698114870
	mov DWORD PTR [edi+164], eax
	mov eax, -1278619122
	mov DWORD PTR [edi+168], eax
	mov eax, -886010445
	mov DWORD PTR [edi+172], eax
	mov eax, 868875271
	mov DWORD PTR [edi+176], eax
	mov eax, 1070917294
	mov DWORD PTR [edi+180], eax
	mov eax, -605436789
	mov DWORD PTR [edi+184], eax
	mov eax, -1428316744
	mov DWORD PTR [edi+188], eax
	mov eax, 0
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
	mov eax, 0
	mov DWORD PTR [edi+304], eax
	mov eax, 0
	mov DWORD PTR [edi+308], eax
	mov eax, 0
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
	mov eax, 0
	mov DWORD PTR [edi+352], eax
	mov eax, 0
	mov DWORD PTR [edi+356], eax
	mov eax, 0
	mov DWORD PTR [edi+360], eax
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov eax, 0
	mov DWORD PTR [edi+368], eax
	mov eax, 0
	mov DWORD PTR [edi+372], eax
	mov eax, 0
	mov DWORD PTR [edi+376], eax
	mov eax, 0
	mov DWORD PTR [edi+380], eax
	mov eax, -1480214771
	mov DWORD PTR [edi+384], eax
	mov eax, -682254423
	mov DWORD PTR [edi+388], eax
	mov eax, -763545222
	mov DWORD PTR [edi+392], eax
	mov eax, -679608112
	mov DWORD PTR [edi+396], eax
	mov eax, 425492249
	mov DWORD PTR [edi+400], eax
	mov eax, 1362255573
	mov DWORD PTR [edi+404], eax
	mov eax, 1681495997
	mov DWORD PTR [edi+408], eax
	mov eax, -2102237953
	mov DWORD PTR [edi+412], eax
	mov eax, -1882392690
	mov DWORD PTR [edi+416], eax
	mov eax, 698114869
	mov DWORD PTR [edi+420], eax
	mov eax, 1278619121
	mov DWORD PTR [edi+424], eax
	mov eax, 886010444
	mov DWORD PTR [edi+428], eax
	mov eax, -868875272
	mov DWORD PTR [edi+432], eax
	mov eax, -1070917295
	mov DWORD PTR [edi+436], eax
	mov eax, 605436788
	mov DWORD PTR [edi+440], eax
	mov eax, 1428316743
	mov DWORD PTR [edi+444], eax
	mov eax, -367999930
	mov DWORD PTR [edi+448], eax
	mov eax, -635467212
	mov DWORD PTR [edi+452], eax
	mov eax, -1347956093
	mov DWORD PTR [edi+456], eax
	mov eax, 350524797
	mov DWORD PTR [edi+460], eax
	mov eax, 1182120875
	mov DWORD PTR [edi+464], eax
	mov eax, 1085295474
	mov DWORD PTR [edi+468], eax
	mov eax, -1636923393
	mov DWORD PTR [edi+472], eax
	mov eax, -812711663
	mov DWORD PTR [edi+476], eax
	mov eax, 1065406919
	mov DWORD PTR [edi+480], eax
	mov eax, -1511247672
	mov DWORD PTR [edi+484], eax
	mov eax, -199325832
	mov DWORD PTR [edi+488], eax
	mov eax, 405606233
	mov DWORD PTR [edi+492], eax
	mov eax, -489650932
	mov DWORD PTR [edi+496], eax
	mov eax, -1204058886
	mov DWORD PTR [edi+500], eax
	mov eax, 578628227
	mov DWORD PTR [edi+504], eax
	mov eax, 1589965191
	mov DWORD PTR [edi+508], eax
	mov eax, 176240041
	mov DWORD PTR [edi+512], eax
	mov eax, -925816212
	mov DWORD PTR [edi+516], eax
	mov eax, -2094512105
	mov DWORD PTR [edi+520], eax
	mov eax, -649057240
	mov DWORD PTR [edi+524], eax
	mov eax, -1577980649
	mov DWORD PTR [edi+528], eax
	mov eax, -176862249
	mov DWORD PTR [edi+532], eax
	mov eax, 765514181
	mov DWORD PTR [edi+536], eax
	mov eax, -663947335
	mov DWORD PTR [edi+540], eax
	mov eax, -1976343511
	mov DWORD PTR [edi+544], eax
	mov eax, -247691167
	mov DWORD PTR [edi+548], eax
	mov eax, -1820477879
	mov DWORD PTR [edi+552], eax
	mov eax, -1738639023
	mov DWORD PTR [edi+556], eax
	mov eax, -279510048
	mov DWORD PTR [edi+560], eax
	mov eax, -325824192
	mov DWORD PTR [edi+564], eax
	mov eax, -109975702
	mov DWORD PTR [edi+568], eax
	mov eax, -1811782301
	mov DWORD PTR [edi+572], eax
	mov eax, 1365367251
	mov DWORD PTR [edi+576], eax
	mov eax, -993094135
	mov DWORD PTR [edi+580], eax
	mov eax, 657195684
	mov DWORD PTR [edi+584], eax
	mov eax, 1748913508
	mov DWORD PTR [edi+588], eax
	mov eax, 1844797071
	mov DWORD PTR [edi+592], eax
	mov eax, 883622932
	mov DWORD PTR [edi+596], eax
	mov eax, 348135368
	mov DWORD PTR [edi+600], eax
	mov eax, -2058333291
	mov DWORD PTR [edi+604], eax
	mov eax, -1872984265
	mov DWORD PTR [edi+608], eax
	mov eax, 607377263
	mov DWORD PTR [edi+612], eax
	mov eax, -210944777
	mov DWORD PTR [edi+616], eax
	mov eax, -1296635337
	mov DWORD PTR [edi+620], eax
	mov eax, 7161203
	mov DWORD PTR [edi+624], eax
	mov eax, -2028161590
	mov DWORD PTR [edi+628], eax
	mov eax, 160754049
	mov DWORD PTR [edi+632], eax
	mov eax, 1512808780
	mov DWORD PTR [edi+636], eax
	mov eax, 621029997
	mov DWORD PTR [edi+640], eax
	mov eax, 797992489
	mov DWORD PTR [edi+644], eax
	mov eax, 1195569957
	mov DWORD PTR [edi+648], eax
	mov eax, 1964564335
	mov DWORD PTR [edi+652], eax
	mov eax, 1283822736
	mov DWORD PTR [edi+656], eax
	mov eax, -1081846445
	mov DWORD PTR [edi+660], eax
	mov eax, 1502530622
	mov DWORD PTR [edi+664], eax
	mov eax, 906938229
	mov DWORD PTR [edi+668], eax
	mov eax, -1880739876
	mov DWORD PTR [edi+672], eax
	mov eax, 2081885064
	mov DWORD PTR [edi+676], eax
	mov eax, -845332596
	mov DWORD PTR [edi+680], eax
	mov eax, 1482500983
	mov DWORD PTR [edi+684], eax
	mov eax, -2029043813
	mov DWORD PTR [edi+688], eax
	mov eax, -1705060390
	mov DWORD PTR [edi+692], eax
	mov eax, 717976193
	mov DWORD PTR [edi+696], eax
	mov eax, -1940862511
	mov DWORD PTR [edi+700], eax
	mov eax, -844622223
	mov DWORD PTR [edi+704], eax
	mov eax, -761042914
	mov DWORD PTR [edi+708], eax
	mov eax, -1792524835
	mov DWORD PTR [edi+712], eax
	mov eax, 143046488
	mov DWORD PTR [edi+716], eax
	mov eax, 867656319
	mov DWORD PTR [edi+720], eax
	mov eax, 1053182928
	mov DWORD PTR [edi+724], eax
	mov eax, 788662248
	mov DWORD PTR [edi+728], eax
	mov eax, -1494077241
	mov DWORD PTR [edi+732], eax
	mov eax, 997789155
	mov DWORD PTR [edi+736], eax
	mov eax, -671495130
	mov DWORD PTR [edi+740], eax
	mov eax, 790019039
	mov DWORD PTR [edi+744], eax
	mov eax, 1916549026
	mov DWORD PTR [edi+748], eax
	mov eax, 424357462
	mov DWORD PTR [edi+752], eax
	mov eax, -1780540596
	mov DWORD PTR [edi+756], eax
	mov eax, 1904478128
	mov DWORD PTR [edi+760], eax
	mov eax, -1483450262
	mov DWORD PTR [edi+764], eax
	mov eax, 1666645911
	mov DWORD PTR [edi+768], eax
	mov eax, 1249405309
	mov DWORD PTR [edi+772], eax
	mov eax, -140368606
	mov DWORD PTR [edi+776], eax
	mov eax, -498193282
	mov DWORD PTR [edi+780], eax
	mov eax, -2141982792
	mov DWORD PTR [edi+784], eax
	mov eax, -1099325722
	mov DWORD PTR [edi+788], eax
	mov eax, -1286153754
	mov DWORD PTR [edi+792], eax
	mov eax, -1430150210
	mov DWORD PTR [edi+796], eax
	mov eax, -1882392689
	mov DWORD PTR [edi+800], eax
	mov eax, 698114869
	mov DWORD PTR [edi+804], eax
	mov eax, 1278619121
	mov DWORD PTR [edi+808], eax
	mov eax, 886010444
	mov DWORD PTR [edi+812], eax
	mov eax, -868875272
	mov DWORD PTR [edi+816], eax
	mov eax, -1070917295
	mov DWORD PTR [edi+820], eax
	mov eax, 605436788
	mov DWORD PTR [edi+824], eax
	mov eax, 1428316743
	mov DWORD PTR [edi+828], eax
	mov eax, 1480214769
	mov DWORD PTR [edi+832], eax
	mov eax, 682254422
	mov DWORD PTR [edi+836], eax
	mov eax, 763545221
	mov DWORD PTR [edi+840], eax
	mov eax, 679608111
	mov DWORD PTR [edi+844], eax
	mov eax, -425492250
	mov DWORD PTR [edi+848], eax
	mov eax, -1362255574
	mov DWORD PTR [edi+852], eax
	mov eax, -1681495998
	mov DWORD PTR [edi+856], eax
	mov eax, 2102237952
	mov DWORD PTR [edi+860], eax
	mov eax, 1882392689
	mov DWORD PTR [edi+864], eax
	mov eax, -698114870
	mov DWORD PTR [edi+868], eax
	mov eax, -1278619122
	mov DWORD PTR [edi+872], eax
	mov eax, -886010445
	mov DWORD PTR [edi+876], eax
	mov eax, 868875271
	mov DWORD PTR [edi+880], eax
	mov eax, 1070917294
	mov DWORD PTR [edi+884], eax
	mov eax, -605436789
	mov DWORD PTR [edi+888], eax
	mov eax, -1428316744
	mov DWORD PTR [edi+892], eax
	mov eax, -1666645913
	mov DWORD PTR [edi+896], eax
	mov eax, -1249405310
	mov DWORD PTR [edi+900], eax
	mov eax, 140368605
	mov DWORD PTR [edi+904], eax
	mov eax, 498193281
	mov DWORD PTR [edi+908], eax
	mov eax, 2141982791
	mov DWORD PTR [edi+912], eax
	mov eax, 1099325721
	mov DWORD PTR [edi+916], eax
	mov eax, 1286153753
	mov DWORD PTR [edi+920], eax
	mov eax, 1430150209
	mov DWORD PTR [edi+924], eax
	mov eax, 1882392688
	mov DWORD PTR [edi+928], eax
	mov eax, -698114870
	mov DWORD PTR [edi+932], eax
	mov eax, -1278619122
	mov DWORD PTR [edi+936], eax
	mov eax, -886010445
	mov DWORD PTR [edi+940], eax
	mov eax, 868875271
	mov DWORD PTR [edi+944], eax
	mov eax, 1070917294
	mov DWORD PTR [edi+948], eax
	mov eax, -605436789
	mov DWORD PTR [edi+952], eax
	mov eax, -1428316744
	mov DWORD PTR [edi+956], eax
	mov eax, 0
	mov DWORD PTR [edi+960], eax
	mov eax, 0
	mov DWORD PTR [edi+964], eax
	mov eax, 0
	mov DWORD PTR [edi+968], eax
	mov eax, 0
	mov DWORD PTR [edi+972], eax
	mov eax, 0
	mov DWORD PTR [edi+976], eax
	mov eax, 0
	mov DWORD PTR [edi+980], eax
	mov eax, 0
	mov DWORD PTR [edi+984], eax
	mov eax, 0
	mov DWORD PTR [edi+988], eax
	mov eax, 0
	mov DWORD PTR [edi+992], eax
	mov eax, 0
	mov DWORD PTR [edi+996], eax
	mov eax, 0
	mov DWORD PTR [edi+1000], eax
	mov eax, 0
	mov DWORD PTR [edi+1004], eax
	mov eax, 0
	mov DWORD PTR [edi+1008], eax
	mov eax, 0
	mov DWORD PTR [edi+1012], eax
	mov eax, 0
	mov DWORD PTR [edi+1016], eax
	mov eax, 0
	mov DWORD PTR [edi+1020], eax
	mov eax, -1480214771
	mov DWORD PTR [edi+1024], eax
	mov eax, -682254423
	mov DWORD PTR [edi+1028], eax
	mov eax, -763545222
	mov DWORD PTR [edi+1032], eax
	mov eax, -679608112
	mov DWORD PTR [edi+1036], eax
	mov eax, 425492249
	mov DWORD PTR [edi+1040], eax
	mov eax, 1362255573
	mov DWORD PTR [edi+1044], eax
	mov eax, 1681495997
	mov DWORD PTR [edi+1048], eax
	mov eax, -2102237953
	mov DWORD PTR [edi+1052], eax
	mov eax, -1882392690
	mov DWORD PTR [edi+1056], eax
	mov eax, 698114869
	mov DWORD PTR [edi+1060], eax
	mov eax, 1278619121
	mov DWORD PTR [edi+1064], eax
	mov eax, 886010444
	mov DWORD PTR [edi+1068], eax
	mov eax, -868875272
	mov DWORD PTR [edi+1072], eax
	mov eax, -1070917295
	mov DWORD PTR [edi+1076], eax
	mov eax, 605436788
	mov DWORD PTR [edi+1080], eax
	mov eax, 1428316743
	mov DWORD PTR [edi+1084], eax
	mov eax, 0
	mov DWORD PTR [edi+1088], eax
	mov eax, 0
	mov DWORD PTR [edi+1092], eax
	mov eax, 0
	mov DWORD PTR [edi+1096], eax
	mov eax, 0
	mov DWORD PTR [edi+1100], eax
	mov eax, 0
	mov DWORD PTR [edi+1104], eax
	mov eax, 0
	mov DWORD PTR [edi+1108], eax
	mov eax, 0
	mov DWORD PTR [edi+1112], eax
	mov eax, 0
	mov DWORD PTR [edi+1116], eax
	mov eax, 0
	mov DWORD PTR [edi+1120], eax
	mov eax, 0
	mov DWORD PTR [edi+1124], eax
	mov eax, 0
	mov DWORD PTR [edi+1128], eax
	mov eax, 0
	mov DWORD PTR [edi+1132], eax
	mov eax, 0
	mov DWORD PTR [edi+1136], eax
	mov eax, 0
	mov DWORD PTR [edi+1140], eax
	mov eax, 0
	mov DWORD PTR [edi+1144], eax
	mov eax, 0
	mov DWORD PTR [edi+1148], eax
	mov eax, -1
	mov DWORD PTR [edi+2880], eax
	mov esi, 64
25:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+2048]
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
	mov esi, 64
26:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+832]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4612], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4613], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4614], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4615], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4616], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4617], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4618], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4619], dl
	test esi, esi
	jne 26b
	mov esi, 64
27:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+896]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+5128], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+5129], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+5130], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+5131], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+5132], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+5133], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+5134], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+5135], dl
	test esi, esi
	jne 27b
	mov ebx, DWORD PTR [esp+12]
	add ebx, 64
	mov eax, DWORD PTR [ebx+60]
	bswap eax
	mov DWORD PTR [edi+1984], eax
	mov eax, DWORD PTR [ebx+56]
	bswap eax
	mov DWORD PTR [edi+1988], eax
	mov eax, DWORD PTR [ebx+52]
	bswap eax
	mov DWORD PTR [edi+1992], eax
	mov eax, DWORD PTR [ebx+48]
	bswap eax
	mov DWORD PTR [edi+1996], eax
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+2000], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+2004], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+2008], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+2012], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+2016], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+2020], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+2024], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+2028], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+2032], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+2036], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+2040], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+2044], eax
	mov eax, 1633219077
	mov DWORD PTR [edi+2560], eax
	mov eax, 1236079690
	mov DWORD PTR [edi+2564], eax
	mov eax, 655718661
	mov DWORD PTR [edi+2568], eax
	mov eax, 2034217264
	mov DWORD PTR [edi+2572], eax
	mov eax, -1873084461
	mov DWORD PTR [edi+2576], eax
	mov eax, 1404565948
	mov DWORD PTR [edi+2580], eax
	mov eax, -2091824603
	mov DWORD PTR [edi+2584], eax
	mov eax, -524182921
	mov DWORD PTR [edi+2588], eax
	mov eax, -712409001
	mov DWORD PTR [edi+2592], eax
	mov eax, 424177624
	mov DWORD PTR [edi+2596], eax
	mov eax, -735314045
	mov DWORD PTR [edi+2600], eax
	mov eax, -1586648481
	mov DWORD PTR [edi+2604], eax
	mov eax, 542568140
	mov DWORD PTR [edi+2608], eax
	mov eax, 539892032
	mov DWORD PTR [edi+2612], eax
	mov eax, -1442880432
	mov DWORD PTR [edi+2616], eax
	mov eax, 1011653893
	mov DWORD PTR [edi+2620], eax
	mov eax, 552151604
	mov DWORD PTR [edi+2624], eax
	mov eax, 1350468502
	mov DWORD PTR [edi+2628], eax
	mov eax, -443655628
	mov DWORD PTR [edi+2632], eax
	mov eax, 10183623
	mov DWORD PTR [edi+2636], eax
	mov eax, 763831466
	mov DWORD PTR [edi+2640], eax
	mov eax, -513039274
	mov DWORD PTR [edi+2644], eax
	mov eax, -1736983038
	mov DWORD PTR [edi+2648], eax
	mov eax, -952225560
	mov DWORD PTR [edi+2652], eax
	mov eax, -31316941
	mov DWORD PTR [edi+2656], eax
	mov eax, -1746924445
	mov DWORD PTR [edi+2660], eax
	mov eax, 1830279197
	mov DWORD PTR [edi+2664], eax
	mov eax, -874883156
	mov DWORD PTR [edi+2668], eax
	mov eax, 196455074
	mov DWORD PTR [edi+2672], eax
	mov eax, 1680020133
	mov DWORD PTR [edi+2676], eax
	mov eax, 1193184935
	mov DWORD PTR [edi+2680], eax
	mov eax, 1783278516
	mov DWORD PTR [edi+2684], eax
	mov ebx, DWORD PTR [esp+4]
	add ebx, 1
	mov eax, DWORD PTR [ebx+60]
	bswap eax
	mov DWORD PTR [edi+2176], eax
	mov eax, DWORD PTR [ebx+56]
	bswap eax
	mov DWORD PTR [edi+2180], eax
	mov eax, DWORD PTR [ebx+52]
	bswap eax
	mov DWORD PTR [edi+2184], eax
	mov eax, DWORD PTR [ebx+48]
	bswap eax
	mov DWORD PTR [edi+2188], eax
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+2192], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+2196], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+2200], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+2204], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+2208], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+2212], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+2216], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+2220], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+2236], eax
	add ebx, 64
	mov eax, DWORD PTR [ebx+60]
	bswap eax
	mov DWORD PTR [edi+2368], eax
	mov eax, DWORD PTR [ebx+56]
	bswap eax
	mov DWORD PTR [edi+2372], eax
	mov eax, DWORD PTR [ebx+52]
	bswap eax
	mov DWORD PTR [edi+2376], eax
	mov eax, DWORD PTR [ebx+48]
	bswap eax
	mov DWORD PTR [edi+2380], eax
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+2384], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+2388], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+2392], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+2396], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+2400], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+2404], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+2408], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+2412], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+2416], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+2420], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+2424], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+2428], eax
	mov ebx, DWORD PTR [esp+4]
	movzx edx, BYTE PTR [ebx]
	xor edx, 4
	sub edx, 1
	sbb edx, edx
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov edx, DWORD PTR [edi+2176]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+2180]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+2184]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+2188]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+2192]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+2196]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+2200]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+2204]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+2208]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+2212]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+2216]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+2220]
	sbb edx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+2224]
	sbb edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+2228]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+2232]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+2236]
	sbb edx, DWORD PTR [edi+124]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov edx, DWORD PTR [edi+2368]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+2372]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+2376]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+2380]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+2384]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+2388]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+2392]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+2396]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+2400]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+2404]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+2408]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+2412]
	sbb edx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+2416]
	sbb edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+2420]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+2424]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+2428]
	sbb edx, DWORD PTR [edi+124]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov eax, 2560
	mov ecx, 2176
	mov edx, 2240
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2560
	mov ecx, 2368
	mov edx, 2304
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2304
	mov ecx, 2304
	mov edx, 2432
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 2240
	mov edx, 2688
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 2688
	mov edx, 2752
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 448
	mov edx, 2688
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2688
	mov ecx, 2752
	mov edx, 2496
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 2496
	mov edx, 2752
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2752
	mov ecx, 2432
	mov edx, 2688
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+2688]
	or edx, DWORD PTR [edi+2692]
	or edx, DWORD PTR [edi+2696]
	or edx, DWORD PTR [edi+2700]
	or edx, DWORD PTR [edi+2704]
	or edx, DWORD PTR [edi+2708]
	or edx, DWORD PTR [edi+2712]
	or edx, DWORD PTR [edi+2716]
	or edx, DWORD PTR [edi+2720]
	or edx, DWORD PTR [edi+2724]
	or edx, DWORD PTR [edi+2728]
	or edx, DWORD PTR [edi+2732]
	or edx, DWORD PTR [edi+2736]
	or edx, DWORD PTR [edi+2740]
	or edx, DWORD PTR [edi+2744]
	or edx, DWORD PTR [edi+2748]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov ecx, DWORD PTR [edi+2880]
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+2240]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2496], eax
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+2244]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2500], eax
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+2248]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2504], eax
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+2252]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2508], eax
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+2256]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2512], eax
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+2260]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2516], eax
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+2264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2520], eax
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+2268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2524], eax
	mov eax, DWORD PTR [edi+608]
	mov edx, DWORD PTR [edi+2272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2528], eax
	mov eax, DWORD PTR [edi+612]
	mov edx, DWORD PTR [edi+2276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2532], eax
	mov eax, DWORD PTR [edi+616]
	mov edx, DWORD PTR [edi+2280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2536], eax
	mov eax, DWORD PTR [edi+620]
	mov edx, DWORD PTR [edi+2284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2540], eax
	mov eax, DWORD PTR [edi+624]
	mov edx, DWORD PTR [edi+2288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2544], eax
	mov eax, DWORD PTR [edi+628]
	mov edx, DWORD PTR [edi+2292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2548], eax
	mov eax, DWORD PTR [edi+632]
	mov edx, DWORD PTR [edi+2296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2552], eax
	mov eax, DWORD PTR [edi+636]
	mov edx, DWORD PTR [edi+2300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2556], eax
	mov eax, DWORD PTR [edi+640]
	mov edx, DWORD PTR [edi+2304]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2816], eax
	mov eax, DWORD PTR [edi+644]
	mov edx, DWORD PTR [edi+2308]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2820], eax
	mov eax, DWORD PTR [edi+648]
	mov edx, DWORD PTR [edi+2312]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2824], eax
	mov eax, DWORD PTR [edi+652]
	mov edx, DWORD PTR [edi+2316]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2828], eax
	mov eax, DWORD PTR [edi+656]
	mov edx, DWORD PTR [edi+2320]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2832], eax
	mov eax, DWORD PTR [edi+660]
	mov edx, DWORD PTR [edi+2324]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2836], eax
	mov eax, DWORD PTR [edi+664]
	mov edx, DWORD PTR [edi+2328]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2840], eax
	mov eax, DWORD PTR [edi+668]
	mov edx, DWORD PTR [edi+2332]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2844], eax
	mov eax, DWORD PTR [edi+672]
	mov edx, DWORD PTR [edi+2336]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2848], eax
	mov eax, DWORD PTR [edi+676]
	mov edx, DWORD PTR [edi+2340]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2852], eax
	mov eax, DWORD PTR [edi+680]
	mov edx, DWORD PTR [edi+2344]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2856], eax
	mov eax, DWORD PTR [edi+684]
	mov edx, DWORD PTR [edi+2348]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2860], eax
	mov eax, DWORD PTR [edi+688]
	mov edx, DWORD PTR [edi+2352]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2864], eax
	mov eax, DWORD PTR [edi+692]
	mov edx, DWORD PTR [edi+2356]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2868], eax
	mov eax, DWORD PTR [edi+696]
	mov edx, DWORD PTR [edi+2360]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2872], eax
	mov eax, DWORD PTR [edi+700]
	mov edx, DWORD PTR [edi+2364]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2876], eax
	mov edx, DWORD PTR [edi+2048]
	sub edx, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+2052]
	sbb edx, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+2056]
	sbb edx, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+2060]
	sbb edx, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+2064]
	sbb edx, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+2068]
	sbb edx, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+2072]
	sbb edx, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+2076]
	sbb edx, DWORD PTR [edi+156]
	mov edx, DWORD PTR [edi+2080]
	sbb edx, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+2084]
	sbb edx, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+2088]
	sbb edx, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+2092]
	sbb edx, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+2096]
	sbb edx, DWORD PTR [edi+176]
	mov edx, DWORD PTR [edi+2100]
	sbb edx, DWORD PTR [edi+180]
	mov edx, DWORD PTR [edi+2104]
	sbb edx, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+2108]
	sbb edx, DWORD PTR [edi+188]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+2048]
	or edx, DWORD PTR [edi+2052]
	or edx, DWORD PTR [edi+2056]
	or edx, DWORD PTR [edi+2060]
	or edx, DWORD PTR [edi+2064]
	or edx, DWORD PTR [edi+2068]
	or edx, DWORD PTR [edi+2072]
	or edx, DWORD PTR [edi+2076]
	or edx, DWORD PTR [edi+2080]
	or edx, DWORD PTR [edi+2084]
	or edx, DWORD PTR [edi+2088]
	or edx, DWORD PTR [edi+2092]
	or edx, DWORD PTR [edi+2096]
	or edx, DWORD PTR [edi+2100]
	or edx, DWORD PTR [edi+2104]
	or edx, DWORD PTR [edi+2108]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov edx, DWORD PTR [edi+1984]
	sub edx, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+1988]
	sbb edx, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+1992]
	sbb edx, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+1996]
	sbb edx, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+2000]
	sbb edx, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+2004]
	sbb edx, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+2008]
	sbb edx, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+2012]
	sbb edx, DWORD PTR [edi+156]
	mov edx, DWORD PTR [edi+2016]
	sbb edx, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+2020]
	sbb edx, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+2024]
	sbb edx, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+2028]
	sbb edx, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+2032]
	sbb edx, DWORD PTR [edi+176]
	mov edx, DWORD PTR [edi+2036]
	sbb edx, DWORD PTR [edi+180]
	mov edx, DWORD PTR [edi+2040]
	sbb edx, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+2044]
	sbb edx, DWORD PTR [edi+188]
	sbb eax, eax
	mov ebx, eax
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
	or edx, DWORD PTR [edi+2032]
	or edx, DWORD PTR [edi+2036]
	or edx, DWORD PTR [edi+2040]
	or edx, DWORD PTR [edi+2044]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov eax, 704
	mov ecx, 1984
	mov edx, 2432
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+1920], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+1924], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+1928], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+1932], eax
	mov eax, DWORD PTR [edi+784]
	mov DWORD PTR [edi+1936], eax
	mov eax, DWORD PTR [edi+788]
	mov DWORD PTR [edi+1940], eax
	mov eax, DWORD PTR [edi+792]
	mov DWORD PTR [edi+1944], eax
	mov eax, DWORD PTR [edi+796]
	mov DWORD PTR [edi+1948], eax
	mov eax, DWORD PTR [edi+800]
	mov DWORD PTR [edi+1952], eax
	mov eax, DWORD PTR [edi+804]
	mov DWORD PTR [edi+1956], eax
	mov eax, DWORD PTR [edi+808]
	mov DWORD PTR [edi+1960], eax
	mov eax, DWORD PTR [edi+812]
	mov DWORD PTR [edi+1964], eax
	mov eax, DWORD PTR [edi+816]
	mov DWORD PTR [edi+1968], eax
	mov eax, DWORD PTR [edi+820]
	mov DWORD PTR [edi+1972], eax
	mov eax, DWORD PTR [edi+824]
	mov DWORD PTR [edi+1976], eax
	mov eax, DWORD PTR [edi+828]
	mov DWORD PTR [edi+1980], eax
	mov esi, 512
28:
	sub esi, 1
	mov eax, 1920
	mov ecx, 1920
	mov edx, 1920
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2432
	mov ecx, 1920
	mov edx, 1984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+5128]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1920]
	mov edx, DWORD PTR [edi+1984]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1920], eax
	mov eax, DWORD PTR [edi+1924]
	mov edx, DWORD PTR [edi+1988]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1924], eax
	mov eax, DWORD PTR [edi+1928]
	mov edx, DWORD PTR [edi+1992]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1928], eax
	mov eax, DWORD PTR [edi+1932]
	mov edx, DWORD PTR [edi+1996]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1932], eax
	mov eax, DWORD PTR [edi+1936]
	mov edx, DWORD PTR [edi+2000]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1936], eax
	mov eax, DWORD PTR [edi+1940]
	mov edx, DWORD PTR [edi+2004]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1940], eax
	mov eax, DWORD PTR [edi+1944]
	mov edx, DWORD PTR [edi+2008]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1944], eax
	mov eax, DWORD PTR [edi+1948]
	mov edx, DWORD PTR [edi+2012]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1948], eax
	mov eax, DWORD PTR [edi+1952]
	mov edx, DWORD PTR [edi+2016]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1952], eax
	mov eax, DWORD PTR [edi+1956]
	mov edx, DWORD PTR [edi+2020]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1956], eax
	mov eax, DWORD PTR [edi+1960]
	mov edx, DWORD PTR [edi+2024]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1960], eax
	mov eax, DWORD PTR [edi+1964]
	mov edx, DWORD PTR [edi+2028]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1964], eax
	mov eax, DWORD PTR [edi+1968]
	mov edx, DWORD PTR [edi+2032]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1968], eax
	mov eax, DWORD PTR [edi+1972]
	mov edx, DWORD PTR [edi+2036]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1972], eax
	mov eax, DWORD PTR [edi+1976]
	mov edx, DWORD PTR [edi+2040]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1976], eax
	mov eax, DWORD PTR [edi+1980]
	mov edx, DWORD PTR [edi+2044]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1980], eax
	test esi, esi
	jne 28b
	mov eax, 704
	mov ecx, 2112
	mov edx, 2624
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 2048
	mov edx, 2560
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1920
	mov ecx, 2624
	mov edx, 2688
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1920
	mov ecx, 2560
	mov edx, 2752
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 320
	mov ecx, 2688
	mov edx, 2240
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 320
	mov ecx, 2752
	mov edx, 2304
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 64
29:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+2240]
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
	mov eax, 176240041
	mov DWORD PTR [edi+2624], eax
	mov eax, -925816212
	mov DWORD PTR [edi+2628], eax
	mov eax, -2094512105
	mov DWORD PTR [edi+2632], eax
	mov eax, -649057240
	mov DWORD PTR [edi+2636], eax
	mov eax, -1577980649
	mov DWORD PTR [edi+2640], eax
	mov eax, -176862249
	mov DWORD PTR [edi+2644], eax
	mov eax, 765514181
	mov DWORD PTR [edi+2648], eax
	mov eax, -663947335
	mov DWORD PTR [edi+2652], eax
	mov eax, -1976343511
	mov DWORD PTR [edi+2656], eax
	mov eax, -247691167
	mov DWORD PTR [edi+2660], eax
	mov eax, -1820477879
	mov DWORD PTR [edi+2664], eax
	mov eax, -1738639023
	mov DWORD PTR [edi+2668], eax
	mov eax, -279510048
	mov DWORD PTR [edi+2672], eax
	mov eax, -325824192
	mov DWORD PTR [edi+2676], eax
	mov eax, -109975702
	mov DWORD PTR [edi+2680], eax
	mov eax, -1811782301
	mov DWORD PTR [edi+2684], eax
	mov eax, 47407277
	mov DWORD PTR [edi+960], eax
	mov eax, 663382300
	mov DWORD PTR [edi+964], eax
	mov eax, -1315259812
	mov DWORD PTR [edi+968], eax
	mov eax, -128583835
	mov DWORD PTR [edi+972], eax
	mov eax, -1108443473
	mov DWORD PTR [edi+976], eax
	mov eax, 642537468
	mov DWORD PTR [edi+980], eax
	mov eax, 1669222193
	mov DWORD PTR [edi+984], eax
	mov eax, -275509312
	mov DWORD PTR [edi+988], eax
	mov eax, -150869305
	mov DWORD PTR [edi+992], eax
	mov eax, 1403448970
	mov DWORD PTR [edi+996], eax
	mov eax, 1550895290
	mov DWORD PTR [edi+1000], eax
	mov eax, -540775196
	mov DWORD PTR [edi+1004], eax
	mov eax, 137462640
	mov DWORD PTR [edi+1008], eax
	mov eax, 2053317786
	mov DWORD PTR [edi+1012], eax
	mov eax, -23371645
	mov DWORD PTR [edi+1016], eax
	mov eax, 1545680791
	mov DWORD PTR [edi+1020], eax
	mov eax, 461142492
	mov DWORD PTR [edi+1024], eax
	mov eax, 509487247
	mov DWORD PTR [edi+1028], eax
	mov eax, -107357619
	mov DWORD PTR [edi+1032], eax
	mov eax, 1497668925
	mov DWORD PTR [edi+1036], eax
	mov eax, -2029911476
	mov DWORD PTR [edi+1040], eax
	mov eax, 614782550
	mov DWORD PTR [edi+1044], eax
	mov eax, -886977842
	mov DWORD PTR [edi+1048], eax
	mov eax, -1897004571
	mov DWORD PTR [edi+1052], eax
	mov eax, 746312169
	mov DWORD PTR [edi+1056], eax
	mov eax, -438166374
	mov DWORD PTR [edi+1060], eax
	mov eax, -1343714299
	mov DWORD PTR [edi+1064], eax
	mov eax, 1707929909
	mov DWORD PTR [edi+1068], eax
	mov eax, -1355900571
	mov DWORD PTR [edi+1072], eax
	mov eax, 1985265959
	mov DWORD PTR [edi+1076], eax
	mov eax, 1584146865
	mov DWORD PTR [edi+1080], eax
	mov eax, 1412145190
	mov DWORD PTR [edi+1084], eax
	mov eax, -1480214771
	mov DWORD PTR [edi+1088], eax
	mov eax, -682254423
	mov DWORD PTR [edi+1092], eax
	mov eax, -763545222
	mov DWORD PTR [edi+1096], eax
	mov eax, -679608112
	mov DWORD PTR [edi+1100], eax
	mov eax, 425492249
	mov DWORD PTR [edi+1104], eax
	mov eax, 1362255573
	mov DWORD PTR [edi+1108], eax
	mov eax, 1681495997
	mov DWORD PTR [edi+1112], eax
	mov eax, -2102237953
	mov DWORD PTR [edi+1116], eax
	mov eax, -1882392690
	mov DWORD PTR [edi+1120], eax
	mov eax, 698114869
	mov DWORD PTR [edi+1124], eax
	mov eax, 1278619121
	mov DWORD PTR [edi+1128], eax
	mov eax, 886010444
	mov DWORD PTR [edi+1132], eax
	mov eax, -868875272
	mov DWORD PTR [edi+1136], eax
	mov eax, -1070917295
	mov DWORD PTR [edi+1140], eax
	mov eax, 605436788
	mov DWORD PTR [edi+1144], eax
	mov eax, 1428316743
	mov DWORD PTR [edi+1148], eax
	mov esi, 74
210:
	sub esi, 1
	cmp esi, 73
	je 211f
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
	jmp 212f
211:
	mov eax, esi
	mov ecx, 7
	mul ecx
	mov ecx, eax
	add ecx, edi
	mov eax, 0
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
212:
	mov eax, esi
	mov ecx, 8192
	mul ecx
	mov edx, DWORD PTR [edi+60]
	add edx, eax
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
	movdqu xmm6, XMMWORD PTR [edx+192]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+208]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 3
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
	movdqu xmm6, XMMWORD PTR [edx+320]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+336]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 4
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
	mov ecx, 5
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
	movdqu xmm6, XMMWORD PTR [edx+576]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+592]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 6
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
	movdqu xmm6, XMMWORD PTR [edx+720]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 7
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
	mov ecx, 8
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
	movdqu xmm6, XMMWORD PTR [edx+960]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+976]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 9
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
	movdqu xmm6, XMMWORD PTR [edx+1088]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1104]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 10
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
	mov ecx, 11
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
	movdqu xmm6, XMMWORD PTR [edx+1360]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 12
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
	movdqu xmm6, XMMWORD PTR [edx+1472]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1488]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 13
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
	movdqu xmm6, XMMWORD PTR [edx+1600]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1616]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 14
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
	movdqu xmm6, XMMWORD PTR [edx+1728]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1744]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 15
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
	movdqu xmm6, XMMWORD PTR [edx+1856]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1872]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 16
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
	movdqu xmm6, XMMWORD PTR [edx+2000]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 17
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
	movdqu xmm6, XMMWORD PTR [edx+2112]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2128]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 18
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
	movdqu xmm6, XMMWORD PTR [edx+2240]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2256]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 19
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
	movdqu xmm6, XMMWORD PTR [edx+2368]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2384]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 20
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
	movdqu xmm6, XMMWORD PTR [edx+2496]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2512]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 21
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
	movdqu xmm6, XMMWORD PTR [edx+2640]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 22
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
	movdqu xmm6, XMMWORD PTR [edx+2752]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2768]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 23
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
	movdqu xmm6, XMMWORD PTR [edx+2880]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2896]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 24
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
	movdqu xmm6, XMMWORD PTR [edx+3008]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3024]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 25
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
	movdqu xmm6, XMMWORD PTR [edx+3136]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3152]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 26
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
	movdqu xmm6, XMMWORD PTR [edx+3280]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 27
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
	movdqu xmm6, XMMWORD PTR [edx+3392]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3408]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 28
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
	movdqu xmm6, XMMWORD PTR [edx+3520]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3536]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 29
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
	movdqu xmm6, XMMWORD PTR [edx+3648]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3664]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 30
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
	movdqu xmm6, XMMWORD PTR [edx+3776]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3792]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 31
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
	movdqu xmm6, XMMWORD PTR [edx+3920]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 32
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
	movdqu xmm6, XMMWORD PTR [edx+4032]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4048]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 33
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4096]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4112]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4128]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4144]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4160]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4176]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 34
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4224]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4240]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4256]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4272]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4288]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4304]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 35
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4352]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4368]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4384]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4400]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4416]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4432]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 36
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
	movdqu xmm6, XMMWORD PTR [edx+4560]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 37
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4608]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4624]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4640]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4656]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4672]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4688]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 38
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4736]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4752]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4768]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4784]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4800]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4816]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 39
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4864]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4880]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4896]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4912]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4928]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4944]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 40
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4992]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5008]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5024]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5040]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5056]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5072]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 41
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5120]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5136]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5152]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5168]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5184]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5200]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 42
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5248]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5264]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5280]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5296]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5312]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5328]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 43
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5376]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5392]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5408]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5424]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5440]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5456]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 44
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5504]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5520]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5536]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5552]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5568]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5584]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 45
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5632]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5648]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5664]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5680]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5696]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5712]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 46
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5760]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5776]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5792]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5808]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5824]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5840]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 47
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5888]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5904]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5920]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5936]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5952]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5968]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 48
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6016]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6032]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6048]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6064]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6080]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6096]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 49
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6144]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6160]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6176]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6192]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6208]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6224]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 50
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6272]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6288]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6304]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6320]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6336]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6352]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 51
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6400]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6416]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6432]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6448]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6464]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6480]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 52
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6528]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6544]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6560]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6576]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6592]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6608]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 53
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6656]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6672]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6688]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6704]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6720]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6736]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 54
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6784]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6800]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6816]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6832]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6848]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6864]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 55
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6912]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6928]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6944]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6960]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6976]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6992]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 56
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7040]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7056]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7072]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7088]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7104]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7120]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 57
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7168]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7184]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7200]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7216]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7232]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7248]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 58
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7296]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7312]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7328]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7344]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7360]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7376]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 59
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7424]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7440]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7456]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7472]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7488]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7504]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 60
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7552]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7568]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7584]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7600]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7616]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7632]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 61
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7680]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7696]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7712]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7728]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7744]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7760]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 62
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7808]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7824]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7840]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7856]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7872]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7888]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 63
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7936]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7952]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7968]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7984]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8000]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8016]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 64
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8064]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8080]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8096]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8112]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8128]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8144]
	pand xmm6, xmm7
	por xmm5, xmm6
	movdqu XMMWORD PTR [edi+1344], xmm0
	movdqu XMMWORD PTR [edi+1360], xmm1
	movdqu XMMWORD PTR [edi+1376], xmm2
	movdqu XMMWORD PTR [edi+1392], xmm3
	movdqu XMMWORD PTR [edi+1408], xmm4
	movdqu XMMWORD PTR [edi+1424], xmm5
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	mov ecx, 1
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
	mov ecx, 2
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+224]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+240]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 3
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+352]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+368]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 4
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
	mov ecx, 5
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+608]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+624]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 6
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+736]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+752]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 7
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
	mov ecx, 8
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+992]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1008]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 9
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
	mov ecx, 10
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
	mov ecx, 11
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1376]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1392]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 12
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1504]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1520]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 13
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1632]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1648]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 14
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
	mov ecx, 15
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1888]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1904]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 16
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2016]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2032]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 17
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2144]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2160]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 18
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2272]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2288]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 19
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
	mov ecx, 20
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2528]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2544]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 21
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2656]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2672]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 22
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2784]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2800]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 23
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2912]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2928]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 24
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
	mov ecx, 25
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3168]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3184]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 26
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3296]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3312]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 27
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3424]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3440]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 28
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3552]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3568]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 29
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
	mov ecx, 30
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3808]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3824]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 31
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3936]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3952]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 32
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4064]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4080]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 33
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4192]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4208]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 34
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
	mov ecx, 35
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4448]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4464]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 36
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4576]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4592]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 37
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4704]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4720]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 38
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4832]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4848]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 39
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
	mov ecx, 40
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5088]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5104]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 41
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5216]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5232]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 42
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5344]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5360]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 43
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5472]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5488]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 44
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5600]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5616]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 45
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5728]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5744]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 46
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5856]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5872]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 47
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5984]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6000]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 48
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6112]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6128]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 49
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6240]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6256]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 50
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6368]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6384]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 51
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6496]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6512]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 52
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6624]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6640]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 53
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6752]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6768]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 54
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6880]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6896]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 55
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7008]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7024]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 56
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7136]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7152]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 57
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7264]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7280]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 58
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7392]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7408]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 59
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7520]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7536]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 60
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7648]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7664]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 61
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7776]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7792]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 62
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7904]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7920]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 63
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8032]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8048]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 64
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8160]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8176]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu XMMWORD PTR [edi+1440], xmm0
	movdqu XMMWORD PTR [edi+1456], xmm1
	mov eax, -1480214771
	mov DWORD PTR [edi+1472], eax
	mov eax, -682254423
	mov DWORD PTR [edi+1476], eax
	mov eax, -763545222
	mov DWORD PTR [edi+1480], eax
	mov eax, -679608112
	mov DWORD PTR [edi+1484], eax
	mov eax, 425492249
	mov DWORD PTR [edi+1488], eax
	mov eax, 1362255573
	mov DWORD PTR [edi+1492], eax
	mov eax, 1681495997
	mov DWORD PTR [edi+1496], eax
	mov eax, -2102237953
	mov DWORD PTR [edi+1500], eax
	mov eax, -1882392690
	mov DWORD PTR [edi+1504], eax
	mov eax, 698114869
	mov DWORD PTR [edi+1508], eax
	mov eax, 1278619121
	mov DWORD PTR [edi+1512], eax
	mov eax, 886010444
	mov DWORD PTR [edi+1516], eax
	mov eax, -868875272
	mov DWORD PTR [edi+1520], eax
	mov eax, -1070917295
	mov DWORD PTR [edi+1524], eax
	mov eax, 605436788
	mov DWORD PTR [edi+1528], eax
	mov eax, 1428316743
	mov DWORD PTR [edi+1532], eax
	mov ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+1408]
	mov edx, DWORD PTR [edi+1472]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1408], eax
	mov eax, DWORD PTR [edi+1412]
	mov edx, DWORD PTR [edi+1476]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1412], eax
	mov eax, DWORD PTR [edi+1416]
	mov edx, DWORD PTR [edi+1480]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1416], eax
	mov eax, DWORD PTR [edi+1420]
	mov edx, DWORD PTR [edi+1484]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1420], eax
	mov eax, DWORD PTR [edi+1424]
	mov edx, DWORD PTR [edi+1488]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1424], eax
	mov eax, DWORD PTR [edi+1428]
	mov edx, DWORD PTR [edi+1492]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1428], eax
	mov eax, DWORD PTR [edi+1432]
	mov edx, DWORD PTR [edi+1496]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1432], eax
	mov eax, DWORD PTR [edi+1436]
	mov edx, DWORD PTR [edi+1500]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1436], eax
	mov eax, DWORD PTR [edi+1440]
	mov edx, DWORD PTR [edi+1504]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1440], eax
	mov eax, DWORD PTR [edi+1444]
	mov edx, DWORD PTR [edi+1508]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1444], eax
	mov eax, DWORD PTR [edi+1448]
	mov edx, DWORD PTR [edi+1512]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1448], eax
	mov eax, DWORD PTR [edi+1452]
	mov edx, DWORD PTR [edi+1516]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1452], eax
	mov eax, DWORD PTR [edi+1456]
	mov edx, DWORD PTR [edi+1520]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+1460]
	mov edx, DWORD PTR [edi+1524]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+1464]
	mov edx, DWORD PTR [edi+1528]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+1468]
	mov edx, DWORD PTR [edi+1532]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1472]
	mov edx, DWORD PTR [edi+256]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1472], eax
	mov eax, DWORD PTR [edi+1476]
	mov edx, DWORD PTR [edi+260]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1476], eax
	mov eax, DWORD PTR [edi+1480]
	mov edx, DWORD PTR [edi+264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1480], eax
	mov eax, DWORD PTR [edi+1484]
	mov edx, DWORD PTR [edi+268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1484], eax
	mov eax, DWORD PTR [edi+1488]
	mov edx, DWORD PTR [edi+272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1488], eax
	mov eax, DWORD PTR [edi+1492]
	mov edx, DWORD PTR [edi+276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1492], eax
	mov eax, DWORD PTR [edi+1496]
	mov edx, DWORD PTR [edi+280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1496], eax
	mov eax, DWORD PTR [edi+1500]
	mov edx, DWORD PTR [edi+284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1500], eax
	mov eax, DWORD PTR [edi+1504]
	mov edx, DWORD PTR [edi+288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1504], eax
	mov eax, DWORD PTR [edi+1508]
	mov edx, DWORD PTR [edi+292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1508], eax
	mov eax, DWORD PTR [edi+1512]
	mov edx, DWORD PTR [edi+296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1512], eax
	mov eax, DWORD PTR [edi+1516]
	mov edx, DWORD PTR [edi+300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1516], eax
	mov eax, DWORD PTR [edi+1520]
	mov edx, DWORD PTR [edi+304]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [edi+1524]
	mov edx, DWORD PTR [edi+308]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1524], eax
	mov eax, DWORD PTR [edi+1528]
	mov edx, DWORD PTR [edi+312]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1532]
	mov edx, DWORD PTR [edi+316]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1532], eax
	mov eax, 1408
	mov ecx, 256
	mov edx, 1984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	cmp esi, 73
	je 213f
	mov eax, esi
	mov ecx, 7
	mul ecx
	mov ecx, eax
	add ecx, edi
	movzx eax, BYTE PTR [ecx+4102]
	sub eax, 1
	mov ecx, eax
	jmp 214f
213:
	mov ecx, -1
214:
	mov eax, DWORD PTR [edi+1408]
	mov edx, DWORD PTR [edi+1984]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1408], eax
	mov eax, DWORD PTR [edi+1412]
	mov edx, DWORD PTR [edi+1988]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1412], eax
	mov eax, DWORD PTR [edi+1416]
	mov edx, DWORD PTR [edi+1992]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1416], eax
	mov eax, DWORD PTR [edi+1420]
	mov edx, DWORD PTR [edi+1996]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1420], eax
	mov eax, DWORD PTR [edi+1424]
	mov edx, DWORD PTR [edi+2000]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1424], eax
	mov eax, DWORD PTR [edi+1428]
	mov edx, DWORD PTR [edi+2004]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1428], eax
	mov eax, DWORD PTR [edi+1432]
	mov edx, DWORD PTR [edi+2008]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1432], eax
	mov eax, DWORD PTR [edi+1436]
	mov edx, DWORD PTR [edi+2012]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1436], eax
	mov eax, DWORD PTR [edi+1440]
	mov edx, DWORD PTR [edi+2016]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1440], eax
	mov eax, DWORD PTR [edi+1444]
	mov edx, DWORD PTR [edi+2020]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1444], eax
	mov eax, DWORD PTR [edi+1448]
	mov edx, DWORD PTR [edi+2024]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1448], eax
	mov eax, DWORD PTR [edi+1452]
	mov edx, DWORD PTR [edi+2028]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1452], eax
	mov eax, DWORD PTR [edi+1456]
	mov edx, DWORD PTR [edi+2032]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+1460]
	mov edx, DWORD PTR [edi+2036]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+1464]
	mov edx, DWORD PTR [edi+2040]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+1468]
	mov edx, DWORD PTR [edi+2044]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1468], eax
	mov eax, 1344
	mov ecx, 960
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1024
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1088
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 960
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1344
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1536
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 960
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1344
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 1024
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1408
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 448
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 2624
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1600
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1600
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1536
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 2624
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1600
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1216
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1856
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1728
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1152
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1728
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1856
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1280
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+960], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+964], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+968], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+972], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [edi+1020], eax
	mov eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+1328]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+1332]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1336]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+1340]
	mov DWORD PTR [edi+1148], eax
	test esi, esi
	jne 210b
	mov eax, DWORD PTR [edi+960]
	mov DWORD PTR [edi+2688], eax
	mov eax, DWORD PTR [edi+964]
	mov DWORD PTR [edi+2692], eax
	mov eax, DWORD PTR [edi+968]
	mov DWORD PTR [edi+2696], eax
	mov eax, DWORD PTR [edi+972]
	mov DWORD PTR [edi+2700], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [edi+2704], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [edi+2708], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+1000]
	mov DWORD PTR [edi+2728], eax
	mov eax, DWORD PTR [edi+1004]
	mov DWORD PTR [edi+2732], eax
	mov eax, DWORD PTR [edi+1008]
	mov DWORD PTR [edi+2736], eax
	mov eax, DWORD PTR [edi+1012]
	mov DWORD PTR [edi+2740], eax
	mov eax, DWORD PTR [edi+1016]
	mov DWORD PTR [edi+2744], eax
	mov eax, DWORD PTR [edi+1020]
	mov DWORD PTR [edi+2748], eax
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [edi+2752], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [edi+2756], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [edi+2760], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [edi+2764], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [edi+2768], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [edi+2772], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [edi+2776], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [edi+2780], eax
	mov eax, DWORD PTR [edi+1056]
	mov DWORD PTR [edi+2784], eax
	mov eax, DWORD PTR [edi+1060]
	mov DWORD PTR [edi+2788], eax
	mov eax, DWORD PTR [edi+1064]
	mov DWORD PTR [edi+2792], eax
	mov eax, DWORD PTR [edi+1068]
	mov DWORD PTR [edi+2796], eax
	mov eax, DWORD PTR [edi+1072]
	mov DWORD PTR [edi+2800], eax
	mov eax, DWORD PTR [edi+1076]
	mov DWORD PTR [edi+2804], eax
	mov eax, DWORD PTR [edi+1080]
	mov DWORD PTR [edi+2808], eax
	mov eax, DWORD PTR [edi+1084]
	mov DWORD PTR [edi+2812], eax
	mov eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+2432], eax
	mov eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+2436], eax
	mov eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+2440], eax
	mov eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+2444], eax
	mov eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+2448], eax
	mov eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+2452], eax
	mov eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+2456], eax
	mov eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+2460], eax
	mov eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+2464], eax
	mov eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+2468], eax
	mov eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+2472], eax
	mov eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+2476], eax
	mov eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+2480], eax
	mov eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+2484], eax
	mov eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+2488], eax
	mov eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+2492], eax
	mov eax, 0
	mov DWORD PTR [edi+960], eax
	mov eax, 0
	mov DWORD PTR [edi+964], eax
	mov eax, 0
	mov DWORD PTR [edi+968], eax
	mov eax, 0
	mov DWORD PTR [edi+972], eax
	mov eax, 0
	mov DWORD PTR [edi+976], eax
	mov eax, 0
	mov DWORD PTR [edi+980], eax
	mov eax, 0
	mov DWORD PTR [edi+984], eax
	mov eax, 0
	mov DWORD PTR [edi+988], eax
	mov eax, 0
	mov DWORD PTR [edi+992], eax
	mov eax, 0
	mov DWORD PTR [edi+996], eax
	mov eax, 0
	mov DWORD PTR [edi+1000], eax
	mov eax, 0
	mov DWORD PTR [edi+1004], eax
	mov eax, 0
	mov DWORD PTR [edi+1008], eax
	mov eax, 0
	mov DWORD PTR [edi+1012], eax
	mov eax, 0
	mov DWORD PTR [edi+1016], eax
	mov eax, 0
	mov DWORD PTR [edi+1020], eax
	mov eax, -1480214771
	mov DWORD PTR [edi+1024], eax
	mov eax, -682254423
	mov DWORD PTR [edi+1028], eax
	mov eax, -763545222
	mov DWORD PTR [edi+1032], eax
	mov eax, -679608112
	mov DWORD PTR [edi+1036], eax
	mov eax, 425492249
	mov DWORD PTR [edi+1040], eax
	mov eax, 1362255573
	mov DWORD PTR [edi+1044], eax
	mov eax, 1681495997
	mov DWORD PTR [edi+1048], eax
	mov eax, -2102237953
	mov DWORD PTR [edi+1052], eax
	mov eax, -1882392690
	mov DWORD PTR [edi+1056], eax
	mov eax, 698114869
	mov DWORD PTR [edi+1060], eax
	mov eax, 1278619121
	mov DWORD PTR [edi+1064], eax
	mov eax, 886010444
	mov DWORD PTR [edi+1068], eax
	mov eax, -868875272
	mov DWORD PTR [edi+1072], eax
	mov eax, -1070917295
	mov DWORD PTR [edi+1076], eax
	mov eax, 605436788
	mov DWORD PTR [edi+1080], eax
	mov eax, 1428316743
	mov DWORD PTR [edi+1084], eax
	mov eax, 0
	mov DWORD PTR [edi+1088], eax
	mov eax, 0
	mov DWORD PTR [edi+1092], eax
	mov eax, 0
	mov DWORD PTR [edi+1096], eax
	mov eax, 0
	mov DWORD PTR [edi+1100], eax
	mov eax, 0
	mov DWORD PTR [edi+1104], eax
	mov eax, 0
	mov DWORD PTR [edi+1108], eax
	mov eax, 0
	mov DWORD PTR [edi+1112], eax
	mov eax, 0
	mov DWORD PTR [edi+1116], eax
	mov eax, 0
	mov DWORD PTR [edi+1120], eax
	mov eax, 0
	mov DWORD PTR [edi+1124], eax
	mov eax, 0
	mov DWORD PTR [edi+1128], eax
	mov eax, 0
	mov DWORD PTR [edi+1132], eax
	mov eax, 0
	mov DWORD PTR [edi+1136], eax
	mov eax, 0
	mov DWORD PTR [edi+1140], eax
	mov eax, 0
	mov DWORD PTR [edi+1144], eax
	mov eax, 0
	mov DWORD PTR [edi+1148], eax
	mov esi, 64
215:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+2304]
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
	jne 215b
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+1344], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+1348], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+1352], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+1356], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+1360], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+1364], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+1368], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+1372], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+1376], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+1380], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+1384], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+1388], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+1392], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+1396], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+1400], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+1404], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+1408], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+1412], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+1416], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+1420], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+1424], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+1428], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+1432], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+1436], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+1440], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+1444], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+1448], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+1452], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+1472], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+1476], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+1480], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+1484], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+1488], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+1492], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+1496], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+1500], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+1504], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+1508], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+1512], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+1516], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+1524], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+1532], eax
	mov esi, 0
	mov eax, esi
	mov ecx, 192
	mul ecx
	mov edx, edi
	add edx, 5644
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+1344]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+1360]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+1376]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+1392]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+1408]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+1424]
	movdqu XMMWORD PTR [edx+80], xmm5
	movdqu xmm0, XMMWORD PTR [edi+1440]
	movdqu XMMWORD PTR [edx+96], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1456]
	movdqu XMMWORD PTR [edx+112], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1472]
	movdqu XMMWORD PTR [edx+128], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1488]
	movdqu XMMWORD PTR [edx+144], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1504]
	movdqu XMMWORD PTR [edx+160], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1520]
	movdqu XMMWORD PTR [edx+176], xmm0
	mov eax, DWORD PTR [edi+2496]
	mov DWORD PTR [edi+1344], eax
	mov eax, DWORD PTR [edi+2500]
	mov DWORD PTR [edi+1348], eax
	mov eax, DWORD PTR [edi+2504]
	mov DWORD PTR [edi+1352], eax
	mov eax, DWORD PTR [edi+2508]
	mov DWORD PTR [edi+1356], eax
	mov eax, DWORD PTR [edi+2512]
	mov DWORD PTR [edi+1360], eax
	mov eax, DWORD PTR [edi+2516]
	mov DWORD PTR [edi+1364], eax
	mov eax, DWORD PTR [edi+2520]
	mov DWORD PTR [edi+1368], eax
	mov eax, DWORD PTR [edi+2524]
	mov DWORD PTR [edi+1372], eax
	mov eax, DWORD PTR [edi+2528]
	mov DWORD PTR [edi+1376], eax
	mov eax, DWORD PTR [edi+2532]
	mov DWORD PTR [edi+1380], eax
	mov eax, DWORD PTR [edi+2536]
	mov DWORD PTR [edi+1384], eax
	mov eax, DWORD PTR [edi+2540]
	mov DWORD PTR [edi+1388], eax
	mov eax, DWORD PTR [edi+2544]
	mov DWORD PTR [edi+1392], eax
	mov eax, DWORD PTR [edi+2548]
	mov DWORD PTR [edi+1396], eax
	mov eax, DWORD PTR [edi+2552]
	mov DWORD PTR [edi+1400], eax
	mov eax, DWORD PTR [edi+2556]
	mov DWORD PTR [edi+1404], eax
	mov eax, DWORD PTR [edi+2816]
	mov DWORD PTR [edi+1408], eax
	mov eax, DWORD PTR [edi+2820]
	mov DWORD PTR [edi+1412], eax
	mov eax, DWORD PTR [edi+2824]
	mov DWORD PTR [edi+1416], eax
	mov eax, DWORD PTR [edi+2828]
	mov DWORD PTR [edi+1420], eax
	mov eax, DWORD PTR [edi+2832]
	mov DWORD PTR [edi+1424], eax
	mov eax, DWORD PTR [edi+2836]
	mov DWORD PTR [edi+1428], eax
	mov eax, DWORD PTR [edi+2840]
	mov DWORD PTR [edi+1432], eax
	mov eax, DWORD PTR [edi+2844]
	mov DWORD PTR [edi+1436], eax
	mov eax, DWORD PTR [edi+2848]
	mov DWORD PTR [edi+1440], eax
	mov eax, DWORD PTR [edi+2852]
	mov DWORD PTR [edi+1444], eax
	mov eax, DWORD PTR [edi+2856]
	mov DWORD PTR [edi+1448], eax
	mov eax, DWORD PTR [edi+2860]
	mov DWORD PTR [edi+1452], eax
	mov eax, DWORD PTR [edi+2864]
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+2868]
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+2872]
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+2876]
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+1472], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+1476], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+1480], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+1484], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+1488], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+1492], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+1496], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+1500], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+1504], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+1508], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+1512], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+1516], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+1524], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+2496]
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [edi+2500]
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [edi+2504]
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [edi+2508]
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [edi+2512]
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [edi+2516]
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [edi+2520]
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [edi+2524]
	mov DWORD PTR [edi+1180], eax
	mov eax, DWORD PTR [edi+2528]
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [edi+2532]
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [edi+2536]
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [edi+2540]
	mov DWORD PTR [edi+1196], eax
	mov eax, DWORD PTR [edi+2544]
	mov DWORD PTR [edi+1200], eax
	mov eax, DWORD PTR [edi+2548]
	mov DWORD PTR [edi+1204], eax
	mov eax, DWORD PTR [edi+2552]
	mov DWORD PTR [edi+1208], eax
	mov eax, DWORD PTR [edi+2556]
	mov DWORD PTR [edi+1212], eax
	mov eax, DWORD PTR [edi+2816]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [edi+2820]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [edi+2824]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+2828]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+2832]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+2836]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+2840]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+2844]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [edi+2848]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+2852]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+2856]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+2860]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [edi+2864]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [edi+2868]
	mov DWORD PTR [edi+1268], eax
	mov eax, DWORD PTR [edi+2872]
	mov DWORD PTR [edi+1272], eax
	mov eax, DWORD PTR [edi+2876]
	mov DWORD PTR [edi+1276], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+1280], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+1284], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+1288], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+1292], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+1296], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+1300], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+1304], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+1308], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+1312], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+1316], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+1320], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+1324], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+1328], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+1332], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+1336], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+1340], eax
	mov esi, 1
	mov eax, esi
	mov ecx, 192
	mul ecx
	mov edx, edi
	add edx, 5644
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+1344]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+1360]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+1376]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+1392]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+1408]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+1424]
	movdqu XMMWORD PTR [edx+80], xmm5
	movdqu xmm0, XMMWORD PTR [edi+1440]
	movdqu XMMWORD PTR [edx+96], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1456]
	movdqu XMMWORD PTR [edx+112], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1472]
	movdqu XMMWORD PTR [edx+128], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1488]
	movdqu XMMWORD PTR [edx+144], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1504]
	movdqu XMMWORD PTR [edx+160], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1520]
	movdqu XMMWORD PTR [edx+176], xmm0
216:
	mov eax, 2496
	mov ecx, 1152
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2816
	mov ecx, 1216
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 384
	mov ecx, 1280
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1152
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2816
	mov ecx, 2496
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1536
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 384
	mov ecx, 2496
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1216
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 384
	mov ecx, 2816
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 448
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 512
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1344
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1600
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1600
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1344
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1536
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 512
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1600
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1408
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1856
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1728
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1344
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1728
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1856
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1472
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	add esi, 1
	mov eax, esi
	mov ecx, 192
	mul ecx
	mov edx, edi
	add edx, 5644
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+1344]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+1360]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+1376]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+1392]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+1408]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+1424]
	movdqu XMMWORD PTR [edx+80], xmm5
	movdqu xmm0, XMMWORD PTR [edi+1440]
	movdqu XMMWORD PTR [edx+96], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1456]
	movdqu XMMWORD PTR [edx+112], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1472]
	movdqu XMMWORD PTR [edx+128], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1488]
	movdqu XMMWORD PTR [edx+144], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1504]
	movdqu XMMWORD PTR [edx+160], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1520]
	movdqu XMMWORD PTR [edx+176], xmm0
	mov eax, DWORD PTR [edi+1344]
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [edi+1348]
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [edi+1352]
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [edi+1356]
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [edi+1360]
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [edi+1364]
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [edi+1368]
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [edi+1372]
	mov DWORD PTR [edi+1180], eax
	mov eax, DWORD PTR [edi+1376]
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [edi+1380]
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [edi+1384]
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [edi+1388]
	mov DWORD PTR [edi+1196], eax
	mov eax, DWORD PTR [edi+1392]
	mov DWORD PTR [edi+1200], eax
	mov eax, DWORD PTR [edi+1396]
	mov DWORD PTR [edi+1204], eax
	mov eax, DWORD PTR [edi+1400]
	mov DWORD PTR [edi+1208], eax
	mov eax, DWORD PTR [edi+1404]
	mov DWORD PTR [edi+1212], eax
	mov eax, DWORD PTR [edi+1408]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [edi+1412]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [edi+1416]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+1420]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+1424]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+1428]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+1432]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+1436]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [edi+1440]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+1444]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+1448]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+1452]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+1268], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+1272], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+1276], eax
	mov eax, DWORD PTR [edi+1472]
	mov DWORD PTR [edi+1280], eax
	mov eax, DWORD PTR [edi+1476]
	mov DWORD PTR [edi+1284], eax
	mov eax, DWORD PTR [edi+1480]
	mov DWORD PTR [edi+1288], eax
	mov eax, DWORD PTR [edi+1484]
	mov DWORD PTR [edi+1292], eax
	mov eax, DWORD PTR [edi+1488]
	mov DWORD PTR [edi+1296], eax
	mov eax, DWORD PTR [edi+1492]
	mov DWORD PTR [edi+1300], eax
	mov eax, DWORD PTR [edi+1496]
	mov DWORD PTR [edi+1304], eax
	mov eax, DWORD PTR [edi+1500]
	mov DWORD PTR [edi+1308], eax
	mov eax, DWORD PTR [edi+1504]
	mov DWORD PTR [edi+1312], eax
	mov eax, DWORD PTR [edi+1508]
	mov DWORD PTR [edi+1316], eax
	mov eax, DWORD PTR [edi+1512]
	mov DWORD PTR [edi+1320], eax
	mov eax, DWORD PTR [edi+1516]
	mov DWORD PTR [edi+1324], eax
	mov eax, DWORD PTR [edi+1520]
	mov DWORD PTR [edi+1328], eax
	mov eax, DWORD PTR [edi+1524]
	mov DWORD PTR [edi+1332], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+1336], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+1340], eax
	cmp esi, 7
	jne 216b
	mov ebx, 8
	mov edx, edi
	add edx, 5644
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
	mov ecx, 3
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
	mov ecx, 4
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
	mov ecx, 5
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
	mov ecx, 6
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
	mov ecx, 7
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
	mov ecx, 8
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
	movdqu XMMWORD PTR [edi+1344], xmm0
	movdqu XMMWORD PTR [edi+1360], xmm1
	movdqu XMMWORD PTR [edi+1376], xmm2
	movdqu XMMWORD PTR [edi+1392], xmm3
	movdqu XMMWORD PTR [edi+1408], xmm4
	movdqu XMMWORD PTR [edi+1424], xmm5
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
	mov ecx, 2
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
	mov ecx, 3
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
	mov ecx, 4
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
	mov ecx, 5
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
	mov ecx, 6
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
	mov ecx, 7
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
	mov ecx, 8
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
	movdqu XMMWORD PTR [edi+1440], xmm0
	movdqu XMMWORD PTR [edi+1456], xmm1
	movdqu XMMWORD PTR [edi+1472], xmm2
	movdqu XMMWORD PTR [edi+1488], xmm3
	movdqu XMMWORD PTR [edi+1504], xmm4
	movdqu XMMWORD PTR [edi+1520], xmm5
	mov eax, DWORD PTR [edi+1344]
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [edi+1348]
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [edi+1352]
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [edi+1356]
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [edi+1360]
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [edi+1364]
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [edi+1368]
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [edi+1372]
	mov DWORD PTR [edi+1180], eax
	mov eax, DWORD PTR [edi+1376]
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [edi+1380]
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [edi+1384]
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [edi+1388]
	mov DWORD PTR [edi+1196], eax
	mov eax, DWORD PTR [edi+1392]
	mov DWORD PTR [edi+1200], eax
	mov eax, DWORD PTR [edi+1396]
	mov DWORD PTR [edi+1204], eax
	mov eax, DWORD PTR [edi+1400]
	mov DWORD PTR [edi+1208], eax
	mov eax, DWORD PTR [edi+1404]
	mov DWORD PTR [edi+1212], eax
	mov eax, DWORD PTR [edi+1408]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [edi+1412]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [edi+1416]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+1420]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+1424]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+1428]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+1432]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+1436]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [edi+1440]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+1444]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+1448]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+1452]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+1268], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+1272], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+1276], eax
	mov eax, DWORD PTR [edi+1472]
	mov DWORD PTR [edi+1280], eax
	mov eax, DWORD PTR [edi+1476]
	mov DWORD PTR [edi+1284], eax
	mov eax, DWORD PTR [edi+1480]
	mov DWORD PTR [edi+1288], eax
	mov eax, DWORD PTR [edi+1484]
	mov DWORD PTR [edi+1292], eax
	mov eax, DWORD PTR [edi+1488]
	mov DWORD PTR [edi+1296], eax
	mov eax, DWORD PTR [edi+1492]
	mov DWORD PTR [edi+1300], eax
	mov eax, DWORD PTR [edi+1496]
	mov DWORD PTR [edi+1304], eax
	mov eax, DWORD PTR [edi+1500]
	mov DWORD PTR [edi+1308], eax
	mov eax, DWORD PTR [edi+1504]
	mov DWORD PTR [edi+1312], eax
	mov eax, DWORD PTR [edi+1508]
	mov DWORD PTR [edi+1316], eax
	mov eax, DWORD PTR [edi+1512]
	mov DWORD PTR [edi+1320], eax
	mov eax, DWORD PTR [edi+1516]
	mov DWORD PTR [edi+1324], eax
	mov eax, DWORD PTR [edi+1520]
	mov DWORD PTR [edi+1328], eax
	mov eax, DWORD PTR [edi+1524]
	mov DWORD PTR [edi+1332], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+1336], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+1340], eax
	mov eax, 2496
	mov ecx, 1152
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2816
	mov ecx, 1216
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 384
	mov ecx, 1280
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1152
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2816
	mov ecx, 2496
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1536
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 384
	mov ecx, 2496
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1216
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 384
	mov ecx, 2816
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 448
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 512
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1344
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1600
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1600
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1344
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1536
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 512
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1600
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1408
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1856
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1728
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1344
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1728
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1856
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1472
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 0
	mov eax, esi
	mov ecx, 192
	mul ecx
	mov edx, edi
	add edx, 5644
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+1344]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+1360]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+1376]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+1392]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+1408]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+1424]
	movdqu XMMWORD PTR [edx+80], xmm5
	movdqu xmm0, XMMWORD PTR [edi+1440]
	movdqu XMMWORD PTR [edx+96], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1456]
	movdqu XMMWORD PTR [edx+112], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1472]
	movdqu XMMWORD PTR [edx+128], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1488]
	movdqu XMMWORD PTR [edx+144], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1504]
	movdqu XMMWORD PTR [edx+160], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1520]
	movdqu XMMWORD PTR [edx+176], xmm0
	mov eax, DWORD PTR [edi+2496]
	mov DWORD PTR [edi+960], eax
	mov eax, DWORD PTR [edi+2500]
	mov DWORD PTR [edi+964], eax
	mov eax, DWORD PTR [edi+2504]
	mov DWORD PTR [edi+968], eax
	mov eax, DWORD PTR [edi+2508]
	mov DWORD PTR [edi+972], eax
	mov eax, DWORD PTR [edi+2512]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+2516]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [edi+2520]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [edi+2524]
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [edi+2528]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+2532]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+2536]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+2540]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [edi+2544]
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+2548]
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+2552]
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+2556]
	mov DWORD PTR [edi+1020], eax
	mov eax, DWORD PTR [edi+2816]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+2820]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+2824]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+2828]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [edi+2832]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [edi+2836]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [edi+2840]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+2844]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [edi+2848]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [edi+2852]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [edi+2856]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [edi+2860]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [edi+2864]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+2868]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+2872]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+2876]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+1148], eax
	mov esi, 127
	mov eax, esi
	mov ecx, 4
	mul ecx
	mov ecx, eax
	add ecx, edi
	movzx eax, BYTE PTR [ecx+4099]
	sub eax, 1
	mov ecx, eax
	mov eax, DWORD PTR [edi+960]
	mov edx, DWORD PTR [edi+256]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+960], eax
	mov eax, DWORD PTR [edi+964]
	mov edx, DWORD PTR [edi+260]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+964], eax
	mov eax, DWORD PTR [edi+968]
	mov edx, DWORD PTR [edi+264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+968], eax
	mov eax, DWORD PTR [edi+972]
	mov edx, DWORD PTR [edi+268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+972], eax
	mov eax, DWORD PTR [edi+976]
	mov edx, DWORD PTR [edi+272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+980]
	mov edx, DWORD PTR [edi+276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [edi+984]
	mov edx, DWORD PTR [edi+280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [edi+988]
	mov edx, DWORD PTR [edi+284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [edi+992]
	mov edx, DWORD PTR [edi+288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+996]
	mov edx, DWORD PTR [edi+292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+1000]
	mov edx, DWORD PTR [edi+296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+1004]
	mov edx, DWORD PTR [edi+300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [edi+1008]
	mov edx, DWORD PTR [edi+304]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+1012]
	mov edx, DWORD PTR [edi+308]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+1016]
	mov edx, DWORD PTR [edi+312]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+1020]
	mov edx, DWORD PTR [edi+316]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1020], eax
	mov eax, DWORD PTR [edi+1024]
	mov edx, DWORD PTR [edi+384]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1028]
	mov edx, DWORD PTR [edi+388]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1032]
	mov edx, DWORD PTR [edi+392]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1036]
	mov edx, DWORD PTR [edi+396]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [edi+1040]
	mov edx, DWORD PTR [edi+400]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [edi+1044]
	mov edx, DWORD PTR [edi+404]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [edi+1048]
	mov edx, DWORD PTR [edi+408]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+1052]
	mov edx, DWORD PTR [edi+412]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [edi+1056]
	mov edx, DWORD PTR [edi+416]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [edi+1060]
	mov edx, DWORD PTR [edi+420]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [edi+1064]
	mov edx, DWORD PTR [edi+424]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [edi+1068]
	mov edx, DWORD PTR [edi+428]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [edi+1072]
	mov edx, DWORD PTR [edi+432]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1076]
	mov edx, DWORD PTR [edi+436]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1080]
	mov edx, DWORD PTR [edi+440]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1084]
	mov edx, DWORD PTR [edi+444]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+1088]
	mov edx, DWORD PTR [edi+256]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1092]
	mov edx, DWORD PTR [edi+260]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1096]
	mov edx, DWORD PTR [edi+264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1100]
	mov edx, DWORD PTR [edi+268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+1104]
	mov edx, DWORD PTR [edi+272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1108]
	mov edx, DWORD PTR [edi+276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1112]
	mov edx, DWORD PTR [edi+280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1116]
	mov edx, DWORD PTR [edi+284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+1120]
	mov edx, DWORD PTR [edi+288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+1124]
	mov edx, DWORD PTR [edi+292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+1128]
	mov edx, DWORD PTR [edi+296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+1132]
	mov edx, DWORD PTR [edi+300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+1136]
	mov edx, DWORD PTR [edi+304]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+1140]
	mov edx, DWORD PTR [edi+308]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1144]
	mov edx, DWORD PTR [edi+312]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+1148]
	mov edx, DWORD PTR [edi+316]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1148], eax
	mov esi, 128
217:
	sub esi, 1
	mov eax, 1088
	mov ecx, 960
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 1088
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1024
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 256
	mov ecx, 1088
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1152
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1216
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1152
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1280
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 448
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1536
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1216
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1472
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1792
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1344
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1344
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1728
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1792
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1664
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1664
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1664
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1408
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1344
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1408
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1344
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1472
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 448
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1536
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1408
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1280
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1792
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1152
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1152
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1728
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1792
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1664
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1664
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1664
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1216
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1152
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1216
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1152
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1280
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 448
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1536
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1216
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1472
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1792
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1344
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1344
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1728
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1792
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1664
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1664
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1664
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1408
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1344
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1408
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1344
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1472
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 448
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1536
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1408
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1280
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1792
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1152
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1152
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1728
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1792
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1664
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1664
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1664
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1216
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1280
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1536
	mov edx, 1088
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 256
	mov ecx, 1216
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1088]
	or edx, DWORD PTR [edi+1092]
	or edx, DWORD PTR [edi+1096]
	or edx, DWORD PTR [edi+1100]
	or edx, DWORD PTR [edi+1104]
	or edx, DWORD PTR [edi+1108]
	or edx, DWORD PTR [edi+1112]
	or edx, DWORD PTR [edi+1116]
	or edx, DWORD PTR [edi+1120]
	or edx, DWORD PTR [edi+1124]
	or edx, DWORD PTR [edi+1128]
	or edx, DWORD PTR [edi+1132]
	or edx, DWORD PTR [edi+1136]
	or edx, DWORD PTR [edi+1140]
	or edx, DWORD PTR [edi+1144]
	or edx, DWORD PTR [edi+1148]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov ecx, edx
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+1024]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+1028]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+1032]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+1036]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+1040]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+1044]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+1048]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+1052]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+1056]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+1060]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+1064]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+1068]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+1072]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+1076]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+1080]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+1084]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1084], eax
	test esi, esi
	je 218f
	mov eax, esi
	mov ecx, 4
	mul ecx
	mov ecx, eax
	add ecx, edi
	movzx ebx, BYTE PTR [ecx+4095]
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
	xor eax, 8
	add eax, 8
	add eax, ebx
	sub eax, 16
	mov edx, eax
	shr edx, 31
	mov ebx, 0
	sub ebx, edx
	xor eax, ebx
	sub eax, ebx
	mov ebx, eax
	and ebx, 7
	add ebx, 1
	jmp 219f
218:
	mov ebx, 0
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
	xor eax, 8
	add eax, 8
	add eax, ebx
	sub eax, 16
	mov edx, eax
	shr edx, 31
	mov ebx, 0
	sub ebx, edx
	xor eax, ebx
	sub eax, ebx
	mov ebx, eax
	and ebx, 7
	add ebx, 1
219:
	mov edx, edi
	add edx, 5644
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
	mov ecx, 3
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
	mov ecx, 4
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
	mov ecx, 5
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
	mov ecx, 6
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
	mov ecx, 7
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
	mov ecx, 8
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
	movdqu XMMWORD PTR [edi+1344], xmm0
	movdqu XMMWORD PTR [edi+1360], xmm1
	movdqu XMMWORD PTR [edi+1376], xmm2
	movdqu XMMWORD PTR [edi+1392], xmm3
	movdqu XMMWORD PTR [edi+1408], xmm4
	movdqu XMMWORD PTR [edi+1424], xmm5
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
	mov ecx, 2
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
	mov ecx, 3
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
	mov ecx, 4
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
	mov ecx, 5
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
	mov ecx, 6
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
	mov ecx, 7
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
	mov ecx, 8
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
	movdqu XMMWORD PTR [edi+1440], xmm0
	movdqu XMMWORD PTR [edi+1456], xmm1
	movdqu XMMWORD PTR [edi+1472], xmm2
	movdqu XMMWORD PTR [edi+1488], xmm3
	movdqu XMMWORD PTR [edi+1504], xmm4
	movdqu XMMWORD PTR [edi+1520], xmm5
	mov ecx, eax
	cmp ecx, 1
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+1344]
	mov edx, DWORD PTR [edi+256]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1344], eax
	mov eax, DWORD PTR [edi+1348]
	mov edx, DWORD PTR [edi+260]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1348], eax
	mov eax, DWORD PTR [edi+1352]
	mov edx, DWORD PTR [edi+264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1352], eax
	mov eax, DWORD PTR [edi+1356]
	mov edx, DWORD PTR [edi+268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1356], eax
	mov eax, DWORD PTR [edi+1360]
	mov edx, DWORD PTR [edi+272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1360], eax
	mov eax, DWORD PTR [edi+1364]
	mov edx, DWORD PTR [edi+276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1364], eax
	mov eax, DWORD PTR [edi+1368]
	mov edx, DWORD PTR [edi+280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1368], eax
	mov eax, DWORD PTR [edi+1372]
	mov edx, DWORD PTR [edi+284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1372], eax
	mov eax, DWORD PTR [edi+1376]
	mov edx, DWORD PTR [edi+288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1376], eax
	mov eax, DWORD PTR [edi+1380]
	mov edx, DWORD PTR [edi+292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1380], eax
	mov eax, DWORD PTR [edi+1384]
	mov edx, DWORD PTR [edi+296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1384], eax
	mov eax, DWORD PTR [edi+1388]
	mov edx, DWORD PTR [edi+300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1388], eax
	mov eax, DWORD PTR [edi+1392]
	mov edx, DWORD PTR [edi+304]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1392], eax
	mov eax, DWORD PTR [edi+1396]
	mov edx, DWORD PTR [edi+308]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1396], eax
	mov eax, DWORD PTR [edi+1400]
	mov edx, DWORD PTR [edi+312]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1400], eax
	mov eax, DWORD PTR [edi+1404]
	mov edx, DWORD PTR [edi+316]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1404], eax
	mov eax, DWORD PTR [edi+1408]
	mov edx, DWORD PTR [edi+384]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1408], eax
	mov eax, DWORD PTR [edi+1412]
	mov edx, DWORD PTR [edi+388]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1412], eax
	mov eax, DWORD PTR [edi+1416]
	mov edx, DWORD PTR [edi+392]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1416], eax
	mov eax, DWORD PTR [edi+1420]
	mov edx, DWORD PTR [edi+396]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1420], eax
	mov eax, DWORD PTR [edi+1424]
	mov edx, DWORD PTR [edi+400]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1424], eax
	mov eax, DWORD PTR [edi+1428]
	mov edx, DWORD PTR [edi+404]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1428], eax
	mov eax, DWORD PTR [edi+1432]
	mov edx, DWORD PTR [edi+408]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1432], eax
	mov eax, DWORD PTR [edi+1436]
	mov edx, DWORD PTR [edi+412]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1436], eax
	mov eax, DWORD PTR [edi+1440]
	mov edx, DWORD PTR [edi+416]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1440], eax
	mov eax, DWORD PTR [edi+1444]
	mov edx, DWORD PTR [edi+420]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1444], eax
	mov eax, DWORD PTR [edi+1448]
	mov edx, DWORD PTR [edi+424]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1448], eax
	mov eax, DWORD PTR [edi+1452]
	mov edx, DWORD PTR [edi+428]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1452], eax
	mov eax, DWORD PTR [edi+1456]
	mov edx, DWORD PTR [edi+432]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+1460]
	mov edx, DWORD PTR [edi+436]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+1464]
	mov edx, DWORD PTR [edi+440]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+1468]
	mov edx, DWORD PTR [edi+444]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1472]
	mov edx, DWORD PTR [edi+256]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1472], eax
	mov eax, DWORD PTR [edi+1476]
	mov edx, DWORD PTR [edi+260]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1476], eax
	mov eax, DWORD PTR [edi+1480]
	mov edx, DWORD PTR [edi+264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1480], eax
	mov eax, DWORD PTR [edi+1484]
	mov edx, DWORD PTR [edi+268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1484], eax
	mov eax, DWORD PTR [edi+1488]
	mov edx, DWORD PTR [edi+272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1488], eax
	mov eax, DWORD PTR [edi+1492]
	mov edx, DWORD PTR [edi+276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1492], eax
	mov eax, DWORD PTR [edi+1496]
	mov edx, DWORD PTR [edi+280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1496], eax
	mov eax, DWORD PTR [edi+1500]
	mov edx, DWORD PTR [edi+284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1500], eax
	mov eax, DWORD PTR [edi+1504]
	mov edx, DWORD PTR [edi+288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1504], eax
	mov eax, DWORD PTR [edi+1508]
	mov edx, DWORD PTR [edi+292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1508], eax
	mov eax, DWORD PTR [edi+1512]
	mov edx, DWORD PTR [edi+296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1512], eax
	mov eax, DWORD PTR [edi+1516]
	mov edx, DWORD PTR [edi+300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1516], eax
	mov eax, DWORD PTR [edi+1520]
	mov edx, DWORD PTR [edi+304]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [edi+1524]
	mov edx, DWORD PTR [edi+308]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1524], eax
	mov eax, DWORD PTR [edi+1528]
	mov edx, DWORD PTR [edi+312]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1532]
	mov edx, DWORD PTR [edi+316]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1532], eax
	mov eax, 256
	mov ecx, 1344
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 256
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 256
	mov ecx, 1472
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	mov ecx, 4
	mul ecx
	mov ecx, eax
	add ecx, edi
	movzx eax, BYTE PTR [ecx+4099]
	sub eax, 1
	mov ecx, eax
	mov eax, DWORD PTR [edi+1216]
	mov edx, DWORD PTR [edi+1408]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1408], eax
	mov eax, DWORD PTR [edi+1220]
	mov edx, DWORD PTR [edi+1412]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1412], eax
	mov eax, DWORD PTR [edi+1224]
	mov edx, DWORD PTR [edi+1416]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1416], eax
	mov eax, DWORD PTR [edi+1228]
	mov edx, DWORD PTR [edi+1420]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1420], eax
	mov eax, DWORD PTR [edi+1232]
	mov edx, DWORD PTR [edi+1424]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1424], eax
	mov eax, DWORD PTR [edi+1236]
	mov edx, DWORD PTR [edi+1428]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1428], eax
	mov eax, DWORD PTR [edi+1240]
	mov edx, DWORD PTR [edi+1432]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1432], eax
	mov eax, DWORD PTR [edi+1244]
	mov edx, DWORD PTR [edi+1436]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1436], eax
	mov eax, DWORD PTR [edi+1248]
	mov edx, DWORD PTR [edi+1440]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1440], eax
	mov eax, DWORD PTR [edi+1252]
	mov edx, DWORD PTR [edi+1444]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1444], eax
	mov eax, DWORD PTR [edi+1256]
	mov edx, DWORD PTR [edi+1448]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1448], eax
	mov eax, DWORD PTR [edi+1260]
	mov edx, DWORD PTR [edi+1452]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1452], eax
	mov eax, DWORD PTR [edi+1264]
	mov edx, DWORD PTR [edi+1456]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+1268]
	mov edx, DWORD PTR [edi+1460]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+1272]
	mov edx, DWORD PTR [edi+1464]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+1276]
	mov edx, DWORD PTR [edi+1468]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1468], eax
	mov eax, 1344
	mov ecx, 960
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1024
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1088
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 960
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1344
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1536
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 960
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1344
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 1024
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1408
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 448
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 512
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1600
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1600
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1536
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 512
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1600
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1216
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1856
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1728
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1152
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1728
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1856
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1280
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+960], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+964], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+968], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+972], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [edi+1020], eax
	mov eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+1328]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+1332]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1336]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+1340]
	mov DWORD PTR [edi+1148], eax
	test esi, esi
	jne 217b
	mov eax, 960
	mov ecx, 2688
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 2752
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 2432
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2752
	mov ecx, 2688
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 960
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1536
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2432
	mov ecx, 2688
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 960
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2432
	mov ecx, 2752
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 1024
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 448
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 512
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1600
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1600
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1536
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 512
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1600
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1216
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1856
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1728
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1152
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1728
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1856
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1280
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+960], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+964], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+968], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+972], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [edi+1020], eax
	mov eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+1328]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+1332]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1336]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+1340]
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+1920], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+1924], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+1928], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+1932], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+1936], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+1940], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+1944], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+1948], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+1952], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+1956], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+1960], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+1964], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+1968], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+1972], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+1976], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+1980], eax
	mov esi, 512
220:
	sub esi, 1
	mov eax, 1920
	mov ecx, 1920
	mov edx, 1920
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 1920
	mov edx, 1984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4612]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1920]
	mov edx, DWORD PTR [edi+1984]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1920], eax
	mov eax, DWORD PTR [edi+1924]
	mov edx, DWORD PTR [edi+1988]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1924], eax
	mov eax, DWORD PTR [edi+1928]
	mov edx, DWORD PTR [edi+1992]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1928], eax
	mov eax, DWORD PTR [edi+1932]
	mov edx, DWORD PTR [edi+1996]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1932], eax
	mov eax, DWORD PTR [edi+1936]
	mov edx, DWORD PTR [edi+2000]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1936], eax
	mov eax, DWORD PTR [edi+1940]
	mov edx, DWORD PTR [edi+2004]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1940], eax
	mov eax, DWORD PTR [edi+1944]
	mov edx, DWORD PTR [edi+2008]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1944], eax
	mov eax, DWORD PTR [edi+1948]
	mov edx, DWORD PTR [edi+2012]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1948], eax
	mov eax, DWORD PTR [edi+1952]
	mov edx, DWORD PTR [edi+2016]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1952], eax
	mov eax, DWORD PTR [edi+1956]
	mov edx, DWORD PTR [edi+2020]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1956], eax
	mov eax, DWORD PTR [edi+1960]
	mov edx, DWORD PTR [edi+2024]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1960], eax
	mov eax, DWORD PTR [edi+1964]
	mov edx, DWORD PTR [edi+2028]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1964], eax
	mov eax, DWORD PTR [edi+1968]
	mov edx, DWORD PTR [edi+2032]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1968], eax
	mov eax, DWORD PTR [edi+1972]
	mov edx, DWORD PTR [edi+2036]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1972], eax
	mov eax, DWORD PTR [edi+1976]
	mov edx, DWORD PTR [edi+2040]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1976], eax
	mov eax, DWORD PTR [edi+1980]
	mov edx, DWORD PTR [edi+2044]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1980], eax
	test esi, esi
	jne 220b
	mov eax, 1920
	mov ecx, 960
	mov edx, 2240
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 320
	mov ecx, 2240
	mov edx, 2304
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 2304
	mov edx, 2496
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2560
	mov ecx, 2496
	mov edx, 2624
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1088]
	or edx, DWORD PTR [edi+1092]
	or edx, DWORD PTR [edi+1096]
	or edx, DWORD PTR [edi+1100]
	or edx, DWORD PTR [edi+1104]
	or edx, DWORD PTR [edi+1108]
	or edx, DWORD PTR [edi+1112]
	or edx, DWORD PTR [edi+1116]
	or edx, DWORD PTR [edi+1120]
	or edx, DWORD PTR [edi+1124]
	or edx, DWORD PTR [edi+1128]
	or edx, DWORD PTR [edi+1132]
	or edx, DWORD PTR [edi+1136]
	or edx, DWORD PTR [edi+1140]
	or edx, DWORD PTR [edi+1144]
	or edx, DWORD PTR [edi+1148]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov edx, DWORD PTR [edi+2624]
	or edx, DWORD PTR [edi+2628]
	or edx, DWORD PTR [edi+2632]
	or edx, DWORD PTR [edi+2636]
	or edx, DWORD PTR [edi+2640]
	or edx, DWORD PTR [edi+2644]
	or edx, DWORD PTR [edi+2648]
	or edx, DWORD PTR [edi+2652]
	or edx, DWORD PTR [edi+2656]
	or edx, DWORD PTR [edi+2660]
	or edx, DWORD PTR [edi+2664]
	or edx, DWORD PTR [edi+2668]
	or edx, DWORD PTR [edi+2672]
	or edx, DWORD PTR [edi+2676]
	or edx, DWORD PTR [edi+2680]
	or edx, DWORD PTR [edi+2684]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov ecx, DWORD PTR [edi+2880]
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

vg_ecdsa_brainpoolp512r1_sign:
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
	sub ecx, 64
	sbb edx, edx
	and ecx, edx
	add ecx, 64
	mov ebx, esp
	add ebx, 296
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
	mov eax, DWORD PTR [esi+60]
	bswap eax
	mov DWORD PTR [esp+220], eax
	sub eax, -1666645911
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esi+56]
	bswap eax
	mov DWORD PTR [esp+216], eax
	sbb eax, -1249405310
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esi+52]
	bswap eax
	mov DWORD PTR [esp+212], eax
	sbb eax, 140368605
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esi+48]
	bswap eax
	mov DWORD PTR [esp+208], eax
	sbb eax, 498193281
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esi+44]
	bswap eax
	mov DWORD PTR [esp+204], eax
	sbb eax, 2141982791
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esi+40]
	bswap eax
	mov DWORD PTR [esp+200], eax
	sbb eax, 1099325721
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esi+36]
	bswap eax
	mov DWORD PTR [esp+196], eax
	sbb eax, 1286153753
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esi+32]
	bswap eax
	mov DWORD PTR [esp+192], eax
	sbb eax, 1430150209
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esi+28]
	bswap eax
	mov DWORD PTR [esp+188], eax
	sbb eax, 1882392688
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esi+24]
	bswap eax
	mov DWORD PTR [esp+184], eax
	sbb eax, -698114870
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esi+20]
	bswap eax
	mov DWORD PTR [esp+180], eax
	sbb eax, -1278619122
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esi+16]
	bswap eax
	mov DWORD PTR [esp+176], eax
	sbb eax, -886010445
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [esp+172], eax
	sbb eax, 868875271
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [esp+168], eax
	sbb eax, 1070917294
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [esp+164], eax
	sbb eax, -605436789
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [esp+160], eax
	sbb eax, -1428316744
	mov DWORD PTR [esp], eax
	sbb edx, edx
	mov eax, DWORD PTR [esp+220]
	mov ecx, DWORD PTR [esp+60]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+220], eax
	mov eax, DWORD PTR [esp+216]
	mov ecx, DWORD PTR [esp+56]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+216], eax
	mov eax, DWORD PTR [esp+212]
	mov ecx, DWORD PTR [esp+52]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+212], eax
	mov eax, DWORD PTR [esp+208]
	mov ecx, DWORD PTR [esp+48]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+208], eax
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
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esp+160]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2381], eax
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
	mov ecx, 129
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
	add eax, 129
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
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esp+160]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2381], eax
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
	mov ecx, 129
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
	add eax, 129
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
	mov eax, 128
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
	cmp eax, 64
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
	call {vg_ecdsa_brainpoolp512r1_sign_k}
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
