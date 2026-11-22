// The functions of `src/internal/vg_ecdsa_p256_sign_k.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p256_sign_k:
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_P256_COMB}
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
	mov eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, -1
	mov DWORD PTR [edi+68], eax
	mov eax, -1
	mov DWORD PTR [edi+72], eax
	mov eax, 0
	mov DWORD PTR [edi+76], eax
	mov eax, 0
	mov DWORD PTR [edi+80], eax
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov eax, 1
	mov DWORD PTR [edi+88], eax
	mov eax, -1
	mov DWORD PTR [edi+92], eax
	mov eax, -60611247
	mov DWORD PTR [edi+96], eax
	mov eax, -205927742
	mov DWORD PTR [edi+100], eax
	mov eax, -1491624316
	mov DWORD PTR [edi+104], eax
	mov eax, -1125713235
	mov DWORD PTR [edi+108], eax
	mov eax, -1
	mov DWORD PTR [edi+112], eax
	mov eax, -1
	mov DWORD PTR [edi+116], eax
	mov eax, 0
	mov DWORD PTR [edi+120], eax
	mov eax, -1
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
	mov eax, 1
	mov DWORD PTR [edi+224], eax
	mov eax, 0
	mov DWORD PTR [edi+228], eax
	mov eax, 0
	mov DWORD PTR [edi+232], eax
	mov eax, -1
	mov DWORD PTR [edi+236], eax
	mov eax, -1
	mov DWORD PTR [edi+240], eax
	mov eax, -1
	mov DWORD PTR [edi+244], eax
	mov eax, -2
	mov DWORD PTR [edi+248], eax
	mov eax, 0
	mov DWORD PTR [edi+252], eax
	mov eax, -4
	mov DWORD PTR [edi+256], eax
	mov eax, -1
	mov DWORD PTR [edi+260], eax
	mov eax, -1
	mov DWORD PTR [edi+264], eax
	mov eax, 3
	mov DWORD PTR [edi+268], eax
	mov eax, 0
	mov DWORD PTR [edi+272], eax
	mov eax, 0
	mov DWORD PTR [edi+276], eax
	mov eax, 4
	mov DWORD PTR [edi+280], eax
	mov eax, -4
	mov DWORD PTR [edi+284], eax
	mov eax, 2102278559
	mov DWORD PTR [edi+288], eax
	mov eax, -1982423514
	mov DWORD PTR [edi+292], eax
	mov eax, 1770820018
	mov DWORD PTR [edi+296], eax
	mov eax, 114299238
	mov DWORD PTR [edi+300], eax
	mov eax, -446460796
	mov DWORD PTR [edi+304], eax
	mov eax, -1327078909
	mov DWORD PTR [edi+308], eax
	mov eax, 227924124
	mov DWORD PTR [edi+312], eax
	mov eax, -1802497447
	mov DWORD PTR [edi+316], eax
	mov eax, 413733948
	mov DWORD PTR [edi+320], eax
	mov eax, 2045194452
	mov DWORD PTR [edi+324], eax
	mov eax, 1609414145
	mov DWORD PTR [edi+328], eax
	mov eax, 1975162364
	mov DWORD PTR [edi+332], eax
	mov eax, 2002920720
	mov DWORD PTR [edi+336], eax
	mov eax, 2046522155
	mov DWORD PTR [edi+340], eax
	mov eax, -1523100218
	mov DWORD PTR [edi+344], eax
	mov eax, 412114806
	mov DWORD PTR [edi+348], eax
	mov eax, -829073910
	mov DWORD PTR [edi+352], eax
	mov eax, -571321513
	mov DWORD PTR [edi+356], eax
	mov eax, -1172708260
	mov DWORD PTR [edi+360], eax
	mov eax, -1958037276
	mov DWORD PTR [edi+364], eax
	mov eax, -584977627
	mov DWORD PTR [edi+368], eax
	mov eax, -756513144
	mov DWORD PTR [edi+372], eax
	mov eax, 629693829
	mov DWORD PTR [edi+376], eax
	mov eax, -2056126696
	mov DWORD PTR [edi+380], eax
	mov eax, -1099305310
	mov DWORD PTR [edi+384], eax
	mov eax, -2094773099
	mov DWORD PTR [edi+388], eax
	mov eax, 1237151654
	mov DWORD PTR [edi+392], eax
	mov eax, 1184463260
	mov DWORD PTR [edi+396], eax
	mov eax, 728493145
	mov DWORD PTR [edi+400], eax
	mov eax, 675656249
	mov DWORD PTR [edi+404], eax
	mov eax, -203860448
	mov DWORD PTR [edi+408], eax
	mov eax, 1726033300
	mov DWORD PTR [edi+412], eax
	mov eax, 60611247
	mov DWORD PTR [edi+416], eax
	mov eax, 205927741
	mov DWORD PTR [edi+420], eax
	mov eax, 1491624315
	mov DWORD PTR [edi+424], eax
	mov eax, 1125713234
	mov DWORD PTR [edi+428], eax
	mov eax, 0
	mov DWORD PTR [edi+432], eax
	mov eax, 0
	mov DWORD PTR [edi+436], eax
	mov eax, -1
	mov DWORD PTR [edi+440], eax
	mov eax, 0
	mov DWORD PTR [edi+444], eax
	mov eax, -3
	mov DWORD PTR [edi+448], eax
	mov eax, -1
	mov DWORD PTR [edi+452], eax
	mov eax, -1
	mov DWORD PTR [edi+456], eax
	mov eax, 0
	mov DWORD PTR [edi+460], eax
	mov eax, 0
	mov DWORD PTR [edi+464], eax
	mov eax, 0
	mov DWORD PTR [edi+468], eax
	mov eax, 1
	mov DWORD PTR [edi+472], eax
	mov eax, -1
	mov DWORD PTR [edi+476], eax
	mov eax, -60611249
	mov DWORD PTR [edi+480], eax
	mov eax, -205927742
	mov DWORD PTR [edi+484], eax
	mov eax, -1491624316
	mov DWORD PTR [edi+488], eax
	mov eax, -1125713235
	mov DWORD PTR [edi+492], eax
	mov eax, -1
	mov DWORD PTR [edi+496], eax
	mov eax, -1
	mov DWORD PTR [edi+500], eax
	mov eax, 0
	mov DWORD PTR [edi+504], eax
	mov eax, -1
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
	mov eax, 1
	mov DWORD PTR [edi+544], eax
	mov eax, 0
	mov DWORD PTR [edi+548], eax
	mov eax, 0
	mov DWORD PTR [edi+552], eax
	mov eax, -1
	mov DWORD PTR [edi+556], eax
	mov eax, -1
	mov DWORD PTR [edi+560], eax
	mov eax, -1
	mov DWORD PTR [edi+564], eax
	mov eax, -2
	mov DWORD PTR [edi+568], eax
	mov eax, 0
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
	call {vg_p256_comb}
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
23:
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
24:
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
	jne 24b
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
	mov ecx, 1
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
	mov ecx, 1
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
	jne 23b
	mov eax, 6144
	mov DWORD PTR [edi+1640], eax
	mov eax, 2560
	mov DWORD PTR [edi+1644], eax
	mov eax, -768
	mov DWORD PTR [edi+1648], eax
	mov eax, -8193
	mov DWORD PTR [edi+1652], eax
	mov eax, -4609
	mov DWORD PTR [edi+1656], eax
	mov eax, -769
	mov DWORD PTR [edi+1660], eax
	mov eax, -4609
	mov DWORD PTR [edi+1664], eax
	mov eax, 6399
	mov DWORD PTR [edi+1668], eax
	mov eax, -6145
	mov DWORD PTR [edi+1676], eax
	mov eax, -2561
	mov DWORD PTR [edi+1680], eax
	mov eax, 767
	mov DWORD PTR [edi+1684], eax
	mov eax, 8193
	mov DWORD PTR [edi+1688], eax
	mov eax, 4608
	mov DWORD PTR [edi+1692], eax
	mov eax, 768
	mov DWORD PTR [edi+1696], eax
	mov eax, 4609
	mov DWORD PTR [edi+1700], eax
	mov eax, -6401
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
	call {vg_p256_mul_mod_p}
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
	call {vg_p256_mul_mod_p}
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
	call {vg_p256_mul_mod_p}
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
	call {vg_p256_add_mod_n}
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
	call {vg_p256_mul_mod_n}
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
25:
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
26:
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
	jne 26b
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
	mov ecx, -301941681
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
	mov ecx, -301941681
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
	jne 25b
	mov eax, 2064231436
	mov DWORD PTR [edi+1640], eax
	mov eax, -857165604
	mov DWORD PTR [edi+1644], eax
	mov eax, 1966206413
	mov DWORD PTR [edi+1648], eax
	mov eax, -159179114
	mov DWORD PTR [edi+1652], eax
	mov eax, 642008044
	mov DWORD PTR [edi+1656], eax
	mov eax, -1511440602
	mov DWORD PTR [edi+1660], eax
	mov eax, 157564087
	mov DWORD PTR [edi+1664], eax
	mov eax, 1108561033
	mov DWORD PTR [edi+1668], eax
	mov eax, -2124842683
	mov DWORD PTR [edi+1676], eax
	mov eax, 651237862
	mov DWORD PTR [edi+1680], eax
	mov eax, 837136567
	mov DWORD PTR [edi+1684], eax
	mov eax, -966534121
	mov DWORD PTR [edi+1688], eax
	mov eax, -642008046
	mov DWORD PTR [edi+1692], eax
	mov eax, 1511440601
	mov DWORD PTR [edi+1696], eax
	mov eax, -157564087
	mov DWORD PTR [edi+1700], eax
	mov eax, -1108561035
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
	call {vg_p256_mul_mod_n}
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
	call {vg_p256_mul_mod_n}
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
	call {vg_p256_mul_mod_n}
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
	call {vg_p256_mul_mod_n}
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
	call {vg_p256_mul_mod_n}
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
	call {vg_p256_add_mod_n}
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
	call {vg_p256_mul_mod_n}
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
	call {vg_p256_mul_mod_n}
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
