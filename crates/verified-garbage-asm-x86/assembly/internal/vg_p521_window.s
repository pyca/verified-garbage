// The functions of `src/internal/vg_p521_window.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_window:
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+1504], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+1508], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+1512], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+1516], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+1524], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+1544], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+1548], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+1552], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+1556], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+1560], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+1564], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+1568], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+1572], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+1576], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+1580], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+1584], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+1588], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+1592], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+1596], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+1600], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+1604], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+1608], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+1612], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+1616], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+1620], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+1624], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+1628], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+1632], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+1636], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+1640], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+1644], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+1648], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+1652], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+1656], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+1660], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+1664], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+1668], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+1672], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+1676], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+1680], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+1684], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+1688], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+1692], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+1696], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+1700], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+1704], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+1708], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+1712], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+1716], eax
	mov esi, 0
	mov eax, esi
	mov ecx, 224
	mul ecx
	mov edx, edi
	add edx, 5836
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+1504]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+1520]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+1536]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+1552]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+1568]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+1584]
	movdqu XMMWORD PTR [edx+80], xmm5
	movdqu xmm0, XMMWORD PTR [edi+1600]
	movdqu XMMWORD PTR [edx+96], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1616]
	movdqu XMMWORD PTR [edx+112], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1632]
	movdqu XMMWORD PTR [edx+128], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1648]
	movdqu XMMWORD PTR [edx+144], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1664]
	movdqu XMMWORD PTR [edx+160], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1680]
	movdqu XMMWORD PTR [edx+176], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1696]
	movdqu XMMWORD PTR [edx+192], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1712]
	movdqu XMMWORD PTR [edx+208], xmm0
	mov eax, DWORD PTR [edi+2800]
	mov DWORD PTR [edi+1504], eax
	mov eax, DWORD PTR [edi+2804]
	mov DWORD PTR [edi+1508], eax
	mov eax, DWORD PTR [edi+2808]
	mov DWORD PTR [edi+1512], eax
	mov eax, DWORD PTR [edi+2812]
	mov DWORD PTR [edi+1516], eax
	mov eax, DWORD PTR [edi+2816]
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [edi+2820]
	mov DWORD PTR [edi+1524], eax
	mov eax, DWORD PTR [edi+2824]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+2828]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+2832]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+2836]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+2840]
	mov DWORD PTR [edi+1544], eax
	mov eax, DWORD PTR [edi+2844]
	mov DWORD PTR [edi+1548], eax
	mov eax, DWORD PTR [edi+2848]
	mov DWORD PTR [edi+1552], eax
	mov eax, DWORD PTR [edi+2852]
	mov DWORD PTR [edi+1556], eax
	mov eax, DWORD PTR [edi+2856]
	mov DWORD PTR [edi+1560], eax
	mov eax, DWORD PTR [edi+2860]
	mov DWORD PTR [edi+1564], eax
	mov eax, DWORD PTR [edi+2864]
	mov DWORD PTR [edi+1568], eax
	mov eax, DWORD PTR [edi+2868]
	mov DWORD PTR [edi+1572], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+1576], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+1580], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+1584], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+1588], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+1592], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+1596], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+1600], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+1604], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+1608], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+1612], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+1616], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+1620], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+1624], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+1628], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+1632], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+1636], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+1640], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+1644], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+1648], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+1652], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+1656], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+1660], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+1664], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+1668], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+1672], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+1676], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+1680], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+1684], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+1688], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+1692], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+1696], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+1700], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+1704], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+1708], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+1712], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+1716], eax
	mov eax, DWORD PTR [edi+2800]
	mov DWORD PTR [edi+1288], eax
	mov eax, DWORD PTR [edi+2804]
	mov DWORD PTR [edi+1292], eax
	mov eax, DWORD PTR [edi+2808]
	mov DWORD PTR [edi+1296], eax
	mov eax, DWORD PTR [edi+2812]
	mov DWORD PTR [edi+1300], eax
	mov eax, DWORD PTR [edi+2816]
	mov DWORD PTR [edi+1304], eax
	mov eax, DWORD PTR [edi+2820]
	mov DWORD PTR [edi+1308], eax
	mov eax, DWORD PTR [edi+2824]
	mov DWORD PTR [edi+1312], eax
	mov eax, DWORD PTR [edi+2828]
	mov DWORD PTR [edi+1316], eax
	mov eax, DWORD PTR [edi+2832]
	mov DWORD PTR [edi+1320], eax
	mov eax, DWORD PTR [edi+2836]
	mov DWORD PTR [edi+1324], eax
	mov eax, DWORD PTR [edi+2840]
	mov DWORD PTR [edi+1328], eax
	mov eax, DWORD PTR [edi+2844]
	mov DWORD PTR [edi+1332], eax
	mov eax, DWORD PTR [edi+2848]
	mov DWORD PTR [edi+1336], eax
	mov eax, DWORD PTR [edi+2852]
	mov DWORD PTR [edi+1340], eax
	mov eax, DWORD PTR [edi+2856]
	mov DWORD PTR [edi+1344], eax
	mov eax, DWORD PTR [edi+2860]
	mov DWORD PTR [edi+1348], eax
	mov eax, DWORD PTR [edi+2864]
	mov DWORD PTR [edi+1352], eax
	mov eax, DWORD PTR [edi+2868]
	mov DWORD PTR [edi+1356], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+1360], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+1364], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+1368], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+1372], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+1376], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+1380], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+1384], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+1388], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+1392], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+1396], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+1400], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+1404], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+1408], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+1412], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+1416], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+1420], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+1424], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+1428], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+1432], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+1436], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+1440], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+1444], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+1448], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+1452], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+1472], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+1476], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+1480], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+1484], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+1488], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+1492], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+1496], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+1500], eax
	mov esi, 1
	mov eax, esi
	mov ecx, 224
	mul ecx
	mov edx, edi
	add edx, 5836
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+1504]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+1520]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+1536]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+1552]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+1568]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+1584]
	movdqu XMMWORD PTR [edx+80], xmm5
	movdqu xmm0, XMMWORD PTR [edi+1600]
	movdqu XMMWORD PTR [edx+96], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1616]
	movdqu XMMWORD PTR [edx+112], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1632]
	movdqu XMMWORD PTR [edx+128], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1648]
	movdqu XMMWORD PTR [edx+144], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1664]
	movdqu XMMWORD PTR [edx+160], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1680]
	movdqu XMMWORD PTR [edx+176], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1696]
	movdqu XMMWORD PTR [edx+192], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1712]
	movdqu XMMWORD PTR [edx+208], xmm0
20:
	mov eax, 2800
	mov ecx, 1288
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3160
	mov ecx, 1360
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 424
	mov ecx, 1432
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1288
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3160
	mov ecx, 2800
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 1936
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1720
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 1936
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1288
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 424
	mov ecx, 2800
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2080
	mov ecx, 2008
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1720
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2080
	mov ecx, 2008
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1360
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 424
	mov ecx, 3160
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1504
	mov ecx, 2080
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1792
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1504
	mov ecx, 2080
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 496
	mov edx, 1648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 568
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1504
	mov edx, 1648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1792
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1792
	mov edx, 1648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1504
	mov edx, 1576
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1720
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 496
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 568
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1720
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 496
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 2008
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 1792
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1576
	mov edx, 1576
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 2080
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1504
	mov ecx, 1936
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1504
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1936
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 2080
	mov edx, 1648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1648
	mov edx, 1648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	add esi, 1
	mov eax, esi
	mov ecx, 224
	mul ecx
	mov edx, edi
	add edx, 5836
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+1504]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+1520]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+1536]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+1552]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+1568]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+1584]
	movdqu XMMWORD PTR [edx+80], xmm5
	movdqu xmm0, XMMWORD PTR [edi+1600]
	movdqu XMMWORD PTR [edx+96], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1616]
	movdqu XMMWORD PTR [edx+112], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1632]
	movdqu XMMWORD PTR [edx+128], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1648]
	movdqu XMMWORD PTR [edx+144], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1664]
	movdqu XMMWORD PTR [edx+160], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1680]
	movdqu XMMWORD PTR [edx+176], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1696]
	movdqu XMMWORD PTR [edx+192], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1712]
	movdqu XMMWORD PTR [edx+208], xmm0
	mov eax, DWORD PTR [edi+1504]
	mov DWORD PTR [edi+1288], eax
	mov eax, DWORD PTR [edi+1508]
	mov DWORD PTR [edi+1292], eax
	mov eax, DWORD PTR [edi+1512]
	mov DWORD PTR [edi+1296], eax
	mov eax, DWORD PTR [edi+1516]
	mov DWORD PTR [edi+1300], eax
	mov eax, DWORD PTR [edi+1520]
	mov DWORD PTR [edi+1304], eax
	mov eax, DWORD PTR [edi+1524]
	mov DWORD PTR [edi+1308], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+1312], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+1316], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+1320], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+1324], eax
	mov eax, DWORD PTR [edi+1544]
	mov DWORD PTR [edi+1328], eax
	mov eax, DWORD PTR [edi+1548]
	mov DWORD PTR [edi+1332], eax
	mov eax, DWORD PTR [edi+1552]
	mov DWORD PTR [edi+1336], eax
	mov eax, DWORD PTR [edi+1556]
	mov DWORD PTR [edi+1340], eax
	mov eax, DWORD PTR [edi+1560]
	mov DWORD PTR [edi+1344], eax
	mov eax, DWORD PTR [edi+1564]
	mov DWORD PTR [edi+1348], eax
	mov eax, DWORD PTR [edi+1568]
	mov DWORD PTR [edi+1352], eax
	mov eax, DWORD PTR [edi+1572]
	mov DWORD PTR [edi+1356], eax
	mov eax, DWORD PTR [edi+1576]
	mov DWORD PTR [edi+1360], eax
	mov eax, DWORD PTR [edi+1580]
	mov DWORD PTR [edi+1364], eax
	mov eax, DWORD PTR [edi+1584]
	mov DWORD PTR [edi+1368], eax
	mov eax, DWORD PTR [edi+1588]
	mov DWORD PTR [edi+1372], eax
	mov eax, DWORD PTR [edi+1592]
	mov DWORD PTR [edi+1376], eax
	mov eax, DWORD PTR [edi+1596]
	mov DWORD PTR [edi+1380], eax
	mov eax, DWORD PTR [edi+1600]
	mov DWORD PTR [edi+1384], eax
	mov eax, DWORD PTR [edi+1604]
	mov DWORD PTR [edi+1388], eax
	mov eax, DWORD PTR [edi+1608]
	mov DWORD PTR [edi+1392], eax
	mov eax, DWORD PTR [edi+1612]
	mov DWORD PTR [edi+1396], eax
	mov eax, DWORD PTR [edi+1616]
	mov DWORD PTR [edi+1400], eax
	mov eax, DWORD PTR [edi+1620]
	mov DWORD PTR [edi+1404], eax
	mov eax, DWORD PTR [edi+1624]
	mov DWORD PTR [edi+1408], eax
	mov eax, DWORD PTR [edi+1628]
	mov DWORD PTR [edi+1412], eax
	mov eax, DWORD PTR [edi+1632]
	mov DWORD PTR [edi+1416], eax
	mov eax, DWORD PTR [edi+1636]
	mov DWORD PTR [edi+1420], eax
	mov eax, DWORD PTR [edi+1640]
	mov DWORD PTR [edi+1424], eax
	mov eax, DWORD PTR [edi+1644]
	mov DWORD PTR [edi+1428], eax
	mov eax, DWORD PTR [edi+1648]
	mov DWORD PTR [edi+1432], eax
	mov eax, DWORD PTR [edi+1652]
	mov DWORD PTR [edi+1436], eax
	mov eax, DWORD PTR [edi+1656]
	mov DWORD PTR [edi+1440], eax
	mov eax, DWORD PTR [edi+1660]
	mov DWORD PTR [edi+1444], eax
	mov eax, DWORD PTR [edi+1664]
	mov DWORD PTR [edi+1448], eax
	mov eax, DWORD PTR [edi+1668]
	mov DWORD PTR [edi+1452], eax
	mov eax, DWORD PTR [edi+1672]
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+1676]
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+1680]
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+1684]
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1688]
	mov DWORD PTR [edi+1472], eax
	mov eax, DWORD PTR [edi+1692]
	mov DWORD PTR [edi+1476], eax
	mov eax, DWORD PTR [edi+1696]
	mov DWORD PTR [edi+1480], eax
	mov eax, DWORD PTR [edi+1700]
	mov DWORD PTR [edi+1484], eax
	mov eax, DWORD PTR [edi+1704]
	mov DWORD PTR [edi+1488], eax
	mov eax, DWORD PTR [edi+1708]
	mov DWORD PTR [edi+1492], eax
	mov eax, DWORD PTR [edi+1712]
	mov DWORD PTR [edi+1496], eax
	mov eax, DWORD PTR [edi+1716]
	mov DWORD PTR [edi+1500], eax
	cmp esi, 7
	jne 20b
	mov ebx, 8
	mov edx, edi
	add edx, 5836
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
	movdqu xmm6, XMMWORD PTR [edx+224]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+240]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+256]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+272]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+288]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+304]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 3
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
	movdqu xmm6, XMMWORD PTR [edx+512]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+528]
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
	mov ecx, 6
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
	movdqu xmm6, XMMWORD PTR [edx+1200]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 7
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
	mov ecx, 8
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1568]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1584]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1600]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1616]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1632]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1648]
	pand xmm6, xmm7
	por xmm5, xmm6
	movdqu XMMWORD PTR [edi+1504], xmm0
	movdqu XMMWORD PTR [edi+1520], xmm1
	movdqu XMMWORD PTR [edi+1536], xmm2
	movdqu XMMWORD PTR [edi+1552], xmm3
	movdqu XMMWORD PTR [edi+1568], xmm4
	movdqu XMMWORD PTR [edi+1584], xmm5
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
	movdqu xmm6, XMMWORD PTR [edx+400]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 3
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+544]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+560]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+576]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+592]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+608]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+624]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 4
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
	mov ecx, 5
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
	movdqu xmm6, XMMWORD PTR [edx+1024]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1040]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1056]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1072]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 6
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
	movdqu xmm6, XMMWORD PTR [edx+1280]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1296]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 7
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
	mov ecx, 8
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
	movdqu XMMWORD PTR [edi+1600], xmm0
	movdqu XMMWORD PTR [edi+1616], xmm1
	movdqu XMMWORD PTR [edi+1632], xmm2
	movdqu XMMWORD PTR [edi+1648], xmm3
	movdqu XMMWORD PTR [edi+1664], xmm4
	movdqu XMMWORD PTR [edi+1680], xmm5
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	mov ecx, 1
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
	mov ecx, 2
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+416]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+432]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 3
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
	mov ecx, 4
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
	mov ecx, 5
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
	mov ecx, 6
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1312]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1328]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 7
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
	mov ecx, 8
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
	movdqu XMMWORD PTR [edi+1696], xmm0
	movdqu XMMWORD PTR [edi+1712], xmm1
	mov eax, DWORD PTR [edi+1504]
	mov DWORD PTR [edi+1288], eax
	mov eax, DWORD PTR [edi+1508]
	mov DWORD PTR [edi+1292], eax
	mov eax, DWORD PTR [edi+1512]
	mov DWORD PTR [edi+1296], eax
	mov eax, DWORD PTR [edi+1516]
	mov DWORD PTR [edi+1300], eax
	mov eax, DWORD PTR [edi+1520]
	mov DWORD PTR [edi+1304], eax
	mov eax, DWORD PTR [edi+1524]
	mov DWORD PTR [edi+1308], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+1312], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+1316], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+1320], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+1324], eax
	mov eax, DWORD PTR [edi+1544]
	mov DWORD PTR [edi+1328], eax
	mov eax, DWORD PTR [edi+1548]
	mov DWORD PTR [edi+1332], eax
	mov eax, DWORD PTR [edi+1552]
	mov DWORD PTR [edi+1336], eax
	mov eax, DWORD PTR [edi+1556]
	mov DWORD PTR [edi+1340], eax
	mov eax, DWORD PTR [edi+1560]
	mov DWORD PTR [edi+1344], eax
	mov eax, DWORD PTR [edi+1564]
	mov DWORD PTR [edi+1348], eax
	mov eax, DWORD PTR [edi+1568]
	mov DWORD PTR [edi+1352], eax
	mov eax, DWORD PTR [edi+1572]
	mov DWORD PTR [edi+1356], eax
	mov eax, DWORD PTR [edi+1576]
	mov DWORD PTR [edi+1360], eax
	mov eax, DWORD PTR [edi+1580]
	mov DWORD PTR [edi+1364], eax
	mov eax, DWORD PTR [edi+1584]
	mov DWORD PTR [edi+1368], eax
	mov eax, DWORD PTR [edi+1588]
	mov DWORD PTR [edi+1372], eax
	mov eax, DWORD PTR [edi+1592]
	mov DWORD PTR [edi+1376], eax
	mov eax, DWORD PTR [edi+1596]
	mov DWORD PTR [edi+1380], eax
	mov eax, DWORD PTR [edi+1600]
	mov DWORD PTR [edi+1384], eax
	mov eax, DWORD PTR [edi+1604]
	mov DWORD PTR [edi+1388], eax
	mov eax, DWORD PTR [edi+1608]
	mov DWORD PTR [edi+1392], eax
	mov eax, DWORD PTR [edi+1612]
	mov DWORD PTR [edi+1396], eax
	mov eax, DWORD PTR [edi+1616]
	mov DWORD PTR [edi+1400], eax
	mov eax, DWORD PTR [edi+1620]
	mov DWORD PTR [edi+1404], eax
	mov eax, DWORD PTR [edi+1624]
	mov DWORD PTR [edi+1408], eax
	mov eax, DWORD PTR [edi+1628]
	mov DWORD PTR [edi+1412], eax
	mov eax, DWORD PTR [edi+1632]
	mov DWORD PTR [edi+1416], eax
	mov eax, DWORD PTR [edi+1636]
	mov DWORD PTR [edi+1420], eax
	mov eax, DWORD PTR [edi+1640]
	mov DWORD PTR [edi+1424], eax
	mov eax, DWORD PTR [edi+1644]
	mov DWORD PTR [edi+1428], eax
	mov eax, DWORD PTR [edi+1648]
	mov DWORD PTR [edi+1432], eax
	mov eax, DWORD PTR [edi+1652]
	mov DWORD PTR [edi+1436], eax
	mov eax, DWORD PTR [edi+1656]
	mov DWORD PTR [edi+1440], eax
	mov eax, DWORD PTR [edi+1660]
	mov DWORD PTR [edi+1444], eax
	mov eax, DWORD PTR [edi+1664]
	mov DWORD PTR [edi+1448], eax
	mov eax, DWORD PTR [edi+1668]
	mov DWORD PTR [edi+1452], eax
	mov eax, DWORD PTR [edi+1672]
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+1676]
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+1680]
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+1684]
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1688]
	mov DWORD PTR [edi+1472], eax
	mov eax, DWORD PTR [edi+1692]
	mov DWORD PTR [edi+1476], eax
	mov eax, DWORD PTR [edi+1696]
	mov DWORD PTR [edi+1480], eax
	mov eax, DWORD PTR [edi+1700]
	mov DWORD PTR [edi+1484], eax
	mov eax, DWORD PTR [edi+1704]
	mov DWORD PTR [edi+1488], eax
	mov eax, DWORD PTR [edi+1708]
	mov DWORD PTR [edi+1492], eax
	mov eax, DWORD PTR [edi+1712]
	mov DWORD PTR [edi+1496], eax
	mov eax, DWORD PTR [edi+1716]
	mov DWORD PTR [edi+1500], eax
	mov eax, 2800
	mov ecx, 1288
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3160
	mov ecx, 1360
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 424
	mov ecx, 1432
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1288
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3160
	mov ecx, 2800
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 1936
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1720
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 1936
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1288
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 424
	mov ecx, 2800
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2080
	mov ecx, 2008
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1720
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2080
	mov ecx, 2008
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1360
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 424
	mov ecx, 3160
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1504
	mov ecx, 2080
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1792
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1504
	mov ecx, 2080
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 496
	mov edx, 1648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 568
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1504
	mov edx, 1648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1792
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1792
	mov edx, 1648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1504
	mov edx, 1576
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1720
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 496
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 568
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1720
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 496
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 2008
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 1792
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1576
	mov edx, 1576
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 2080
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1504
	mov ecx, 1936
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1504
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1936
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 2080
	mov edx, 1648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1648
	mov edx, 1648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 0
	mov eax, esi
	mov ecx, 224
	mul ecx
	mov edx, edi
	add edx, 5836
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+1504]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+1520]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+1536]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+1552]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+1568]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+1584]
	movdqu XMMWORD PTR [edx+80], xmm5
	movdqu xmm0, XMMWORD PTR [edi+1600]
	movdqu XMMWORD PTR [edx+96], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1616]
	movdqu XMMWORD PTR [edx+112], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1632]
	movdqu XMMWORD PTR [edx+128], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1648]
	movdqu XMMWORD PTR [edx+144], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1664]
	movdqu XMMWORD PTR [edx+160], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1680]
	movdqu XMMWORD PTR [edx+176], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1696]
	movdqu XMMWORD PTR [edx+192], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1712]
	movdqu XMMWORD PTR [edx+208], xmm0
	mov eax, DWORD PTR [edi+2800]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+2804]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+2808]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+2812]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+2816]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+2820]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+2824]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+2828]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+2832]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+2836]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+2840]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+2844]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+2848]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+2852]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+2856]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+2860]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+2864]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+2868]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+1180], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+1196], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+1200], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+1204], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+1208], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+1212], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+1268], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+1272], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+1276], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+1280], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+1284], eax
	mov esi, 131
	mov eax, esi
	mov ecx, 4
	mul ecx
	mov ecx, eax
	add ecx, edi
	movzx eax, BYTE PTR [ecx+4099]
	sub eax, 1
	mov ecx, eax
	mov eax, DWORD PTR [edi+1072]
	mov edx, DWORD PTR [edi+280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1076]
	mov edx, DWORD PTR [edi+284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1080]
	mov edx, DWORD PTR [edi+288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1084]
	mov edx, DWORD PTR [edi+292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+1088]
	mov edx, DWORD PTR [edi+296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1092]
	mov edx, DWORD PTR [edi+300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1096]
	mov edx, DWORD PTR [edi+304]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1100]
	mov edx, DWORD PTR [edi+308]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+1104]
	mov edx, DWORD PTR [edi+312]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1108]
	mov edx, DWORD PTR [edi+316]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1112]
	mov edx, DWORD PTR [edi+320]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1116]
	mov edx, DWORD PTR [edi+324]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+1120]
	mov edx, DWORD PTR [edi+328]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+1124]
	mov edx, DWORD PTR [edi+332]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+1128]
	mov edx, DWORD PTR [edi+336]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+1132]
	mov edx, DWORD PTR [edi+340]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+1136]
	mov edx, DWORD PTR [edi+344]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+1140]
	mov edx, DWORD PTR [edi+348]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1144]
	mov edx, DWORD PTR [edi+424]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+1148]
	mov edx, DWORD PTR [edi+428]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [edi+1152]
	mov edx, DWORD PTR [edi+432]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [edi+1156]
	mov edx, DWORD PTR [edi+436]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [edi+1160]
	mov edx, DWORD PTR [edi+440]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [edi+1164]
	mov edx, DWORD PTR [edi+444]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [edi+1168]
	mov edx, DWORD PTR [edi+448]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [edi+1172]
	mov edx, DWORD PTR [edi+452]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [edi+1176]
	mov edx, DWORD PTR [edi+456]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [edi+1180]
	mov edx, DWORD PTR [edi+460]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1180], eax
	mov eax, DWORD PTR [edi+1184]
	mov edx, DWORD PTR [edi+464]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [edi+1188]
	mov edx, DWORD PTR [edi+468]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [edi+1192]
	mov edx, DWORD PTR [edi+472]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [edi+1196]
	mov edx, DWORD PTR [edi+476]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1196], eax
	mov eax, DWORD PTR [edi+1200]
	mov edx, DWORD PTR [edi+480]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1200], eax
	mov eax, DWORD PTR [edi+1204]
	mov edx, DWORD PTR [edi+484]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1204], eax
	mov eax, DWORD PTR [edi+1208]
	mov edx, DWORD PTR [edi+488]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1208], eax
	mov eax, DWORD PTR [edi+1212]
	mov edx, DWORD PTR [edi+492]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1212], eax
	mov eax, DWORD PTR [edi+1216]
	mov edx, DWORD PTR [edi+280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [edi+1220]
	mov edx, DWORD PTR [edi+284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [edi+1224]
	mov edx, DWORD PTR [edi+288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+1228]
	mov edx, DWORD PTR [edi+292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+1232]
	mov edx, DWORD PTR [edi+296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+1236]
	mov edx, DWORD PTR [edi+300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+1240]
	mov edx, DWORD PTR [edi+304]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+1244]
	mov edx, DWORD PTR [edi+308]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [edi+1248]
	mov edx, DWORD PTR [edi+312]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+1252]
	mov edx, DWORD PTR [edi+316]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+1256]
	mov edx, DWORD PTR [edi+320]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+1260]
	mov edx, DWORD PTR [edi+324]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [edi+1264]
	mov edx, DWORD PTR [edi+328]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [edi+1268]
	mov edx, DWORD PTR [edi+332]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1268], eax
	mov eax, DWORD PTR [edi+1272]
	mov edx, DWORD PTR [edi+336]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1272], eax
	mov eax, DWORD PTR [edi+1276]
	mov edx, DWORD PTR [edi+340]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1276], eax
	mov eax, DWORD PTR [edi+1280]
	mov edx, DWORD PTR [edi+344]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1280], eax
	mov eax, DWORD PTR [edi+1284]
	mov edx, DWORD PTR [edi+348]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1284], eax
	mov esi, 132
21:
	sub esi, 1
	mov eax, 1216
	mov ecx, 1072
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1216
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1144
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 280
	mov ecx, 1216
	mov edx, 1432
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1432
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1360
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
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
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1288
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1288
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1288
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1504
	mov ecx, 1936
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1936
	mov ecx, 1936
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1936
	mov ecx, 1504
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1864
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1360
	mov edx, 1648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1648
	mov edx, 1648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1936
	mov ecx, 1936
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1504
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1504
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1504
	mov ecx, 1864
	mov edx, 1576
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1576
	mov ecx, 1936
	mov edx, 1576
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
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
	call {vg_p521_mul_mod_p}
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
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1576
	mov edx, 1576
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1648
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1576
	mov ecx, 1576
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
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
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1504
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1504
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1504
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1288
	mov ecx, 1936
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1936
	mov ecx, 1936
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1936
	mov ecx, 1288
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1864
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1576
	mov edx, 1432
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1432
	mov edx, 1432
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1936
	mov ecx, 1936
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1288
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1288
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1288
	mov ecx, 1864
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1936
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
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
	call {vg_p521_mul_mod_p}
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
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1360
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1432
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1360
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
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
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1288
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1288
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1288
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1504
	mov ecx, 1936
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1936
	mov ecx, 1936
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1936
	mov ecx, 1504
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1864
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1360
	mov edx, 1648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1648
	mov edx, 1648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1936
	mov ecx, 1936
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1504
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1504
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1504
	mov ecx, 1864
	mov edx, 1576
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1576
	mov ecx, 1936
	mov edx, 1576
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
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
	call {vg_p521_mul_mod_p}
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
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1576
	mov edx, 1576
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1648
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1576
	mov ecx, 1576
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
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
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1504
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1504
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1504
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1288
	mov ecx, 1936
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1936
	mov ecx, 1936
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1936
	mov ecx, 1288
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1864
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1576
	mov edx, 1432
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1432
	mov edx, 1432
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1936
	mov ecx, 1936
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1288
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1288
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1288
	mov ecx, 1864
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1936
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
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
	call {vg_p521_mul_mod_p}
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
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1360
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1288
	mov edx, 1072
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1432
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1720
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 280
	mov ecx, 1360
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1216]
	or edx, DWORD PTR [edi+1220]
	or edx, DWORD PTR [edi+1224]
	or edx, DWORD PTR [edi+1228]
	or edx, DWORD PTR [edi+1232]
	or edx, DWORD PTR [edi+1236]
	or edx, DWORD PTR [edi+1240]
	or edx, DWORD PTR [edi+1244]
	or edx, DWORD PTR [edi+1248]
	or edx, DWORD PTR [edi+1252]
	or edx, DWORD PTR [edi+1256]
	or edx, DWORD PTR [edi+1260]
	or edx, DWORD PTR [edi+1264]
	or edx, DWORD PTR [edi+1268]
	or edx, DWORD PTR [edi+1272]
	or edx, DWORD PTR [edi+1276]
	or edx, DWORD PTR [edi+1280]
	or edx, DWORD PTR [edi+1284]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov ecx, edx
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+1144]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+1148]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+1152]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+1156]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+1160]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+1164]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+1168]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+1172]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+1176]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+1180]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1180], eax
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+1184]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+1188]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+1192]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+1196]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1196], eax
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+1200]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1200], eax
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+1204]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1204], eax
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+1208]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1208], eax
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+1212]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1212], eax
	test esi, esi
	je 22f
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
	jmp 23f
22:
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
23:
	mov edx, edi
	add edx, 5836
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
	movdqu xmm6, XMMWORD PTR [edx+224]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+240]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+256]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+272]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+288]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+304]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 3
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
	movdqu xmm6, XMMWORD PTR [edx+512]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+528]
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
	mov ecx, 6
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
	movdqu xmm6, XMMWORD PTR [edx+1200]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 7
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
	mov ecx, 8
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1568]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1584]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1600]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1616]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1632]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1648]
	pand xmm6, xmm7
	por xmm5, xmm6
	movdqu XMMWORD PTR [edi+1504], xmm0
	movdqu XMMWORD PTR [edi+1520], xmm1
	movdqu XMMWORD PTR [edi+1536], xmm2
	movdqu XMMWORD PTR [edi+1552], xmm3
	movdqu XMMWORD PTR [edi+1568], xmm4
	movdqu XMMWORD PTR [edi+1584], xmm5
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
	movdqu xmm6, XMMWORD PTR [edx+400]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 3
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+544]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+560]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+576]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+592]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+608]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+624]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 4
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
	mov ecx, 5
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
	movdqu xmm6, XMMWORD PTR [edx+1024]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1040]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1056]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1072]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 6
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
	movdqu xmm6, XMMWORD PTR [edx+1280]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1296]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 7
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
	mov ecx, 8
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
	movdqu XMMWORD PTR [edi+1600], xmm0
	movdqu XMMWORD PTR [edi+1616], xmm1
	movdqu XMMWORD PTR [edi+1632], xmm2
	movdqu XMMWORD PTR [edi+1648], xmm3
	movdqu XMMWORD PTR [edi+1664], xmm4
	movdqu XMMWORD PTR [edi+1680], xmm5
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	mov ecx, 1
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
	mov ecx, 2
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+416]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+432]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 3
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
	mov ecx, 4
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
	mov ecx, 5
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
	mov ecx, 6
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1312]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1328]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 7
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
	mov ecx, 8
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
	movdqu XMMWORD PTR [edi+1696], xmm0
	movdqu XMMWORD PTR [edi+1712], xmm1
	mov ecx, eax
	cmp ecx, 1
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+1504]
	mov edx, DWORD PTR [edi+280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1504], eax
	mov eax, DWORD PTR [edi+1508]
	mov edx, DWORD PTR [edi+284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1508], eax
	mov eax, DWORD PTR [edi+1512]
	mov edx, DWORD PTR [edi+288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1512], eax
	mov eax, DWORD PTR [edi+1516]
	mov edx, DWORD PTR [edi+292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1516], eax
	mov eax, DWORD PTR [edi+1520]
	mov edx, DWORD PTR [edi+296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [edi+1524]
	mov edx, DWORD PTR [edi+300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1524], eax
	mov eax, DWORD PTR [edi+1528]
	mov edx, DWORD PTR [edi+304]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1532]
	mov edx, DWORD PTR [edi+308]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1536]
	mov edx, DWORD PTR [edi+312]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1540]
	mov edx, DWORD PTR [edi+316]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1544]
	mov edx, DWORD PTR [edi+320]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1544], eax
	mov eax, DWORD PTR [edi+1548]
	mov edx, DWORD PTR [edi+324]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1548], eax
	mov eax, DWORD PTR [edi+1552]
	mov edx, DWORD PTR [edi+328]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1552], eax
	mov eax, DWORD PTR [edi+1556]
	mov edx, DWORD PTR [edi+332]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1556], eax
	mov eax, DWORD PTR [edi+1560]
	mov edx, DWORD PTR [edi+336]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1560], eax
	mov eax, DWORD PTR [edi+1564]
	mov edx, DWORD PTR [edi+340]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1564], eax
	mov eax, DWORD PTR [edi+1568]
	mov edx, DWORD PTR [edi+344]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1568], eax
	mov eax, DWORD PTR [edi+1572]
	mov edx, DWORD PTR [edi+348]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1572], eax
	mov eax, DWORD PTR [edi+1576]
	mov edx, DWORD PTR [edi+424]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1576], eax
	mov eax, DWORD PTR [edi+1580]
	mov edx, DWORD PTR [edi+428]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1580], eax
	mov eax, DWORD PTR [edi+1584]
	mov edx, DWORD PTR [edi+432]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1584], eax
	mov eax, DWORD PTR [edi+1588]
	mov edx, DWORD PTR [edi+436]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1588], eax
	mov eax, DWORD PTR [edi+1592]
	mov edx, DWORD PTR [edi+440]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1592], eax
	mov eax, DWORD PTR [edi+1596]
	mov edx, DWORD PTR [edi+444]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1596], eax
	mov eax, DWORD PTR [edi+1600]
	mov edx, DWORD PTR [edi+448]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1600], eax
	mov eax, DWORD PTR [edi+1604]
	mov edx, DWORD PTR [edi+452]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1604], eax
	mov eax, DWORD PTR [edi+1608]
	mov edx, DWORD PTR [edi+456]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1608], eax
	mov eax, DWORD PTR [edi+1612]
	mov edx, DWORD PTR [edi+460]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1612], eax
	mov eax, DWORD PTR [edi+1616]
	mov edx, DWORD PTR [edi+464]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1616], eax
	mov eax, DWORD PTR [edi+1620]
	mov edx, DWORD PTR [edi+468]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1620], eax
	mov eax, DWORD PTR [edi+1624]
	mov edx, DWORD PTR [edi+472]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1624], eax
	mov eax, DWORD PTR [edi+1628]
	mov edx, DWORD PTR [edi+476]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1628], eax
	mov eax, DWORD PTR [edi+1632]
	mov edx, DWORD PTR [edi+480]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1632], eax
	mov eax, DWORD PTR [edi+1636]
	mov edx, DWORD PTR [edi+484]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1636], eax
	mov eax, DWORD PTR [edi+1640]
	mov edx, DWORD PTR [edi+488]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1640], eax
	mov eax, DWORD PTR [edi+1644]
	mov edx, DWORD PTR [edi+492]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1644], eax
	mov eax, DWORD PTR [edi+1648]
	mov edx, DWORD PTR [edi+280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1648], eax
	mov eax, DWORD PTR [edi+1652]
	mov edx, DWORD PTR [edi+284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1652], eax
	mov eax, DWORD PTR [edi+1656]
	mov edx, DWORD PTR [edi+288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1656], eax
	mov eax, DWORD PTR [edi+1660]
	mov edx, DWORD PTR [edi+292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1660], eax
	mov eax, DWORD PTR [edi+1664]
	mov edx, DWORD PTR [edi+296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1664], eax
	mov eax, DWORD PTR [edi+1668]
	mov edx, DWORD PTR [edi+300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1668], eax
	mov eax, DWORD PTR [edi+1672]
	mov edx, DWORD PTR [edi+304]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1672], eax
	mov eax, DWORD PTR [edi+1676]
	mov edx, DWORD PTR [edi+308]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1676], eax
	mov eax, DWORD PTR [edi+1680]
	mov edx, DWORD PTR [edi+312]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1680], eax
	mov eax, DWORD PTR [edi+1684]
	mov edx, DWORD PTR [edi+316]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1684], eax
	mov eax, DWORD PTR [edi+1688]
	mov edx, DWORD PTR [edi+320]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1688], eax
	mov eax, DWORD PTR [edi+1692]
	mov edx, DWORD PTR [edi+324]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1692], eax
	mov eax, DWORD PTR [edi+1696]
	mov edx, DWORD PTR [edi+328]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1696], eax
	mov eax, DWORD PTR [edi+1700]
	mov edx, DWORD PTR [edi+332]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1700], eax
	mov eax, DWORD PTR [edi+1704]
	mov edx, DWORD PTR [edi+336]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1704], eax
	mov eax, DWORD PTR [edi+1708]
	mov edx, DWORD PTR [edi+340]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1708], eax
	mov eax, DWORD PTR [edi+1712]
	mov edx, DWORD PTR [edi+344]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1712], eax
	mov eax, DWORD PTR [edi+1716]
	mov edx, DWORD PTR [edi+348]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1716], eax
	mov eax, 280
	mov ecx, 1504
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1576
	mov ecx, 280
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 280
	mov ecx, 1648
	mov edx, 1432
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
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
	mov eax, DWORD PTR [edi+1360]
	mov edx, DWORD PTR [edi+1576]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1576], eax
	mov eax, DWORD PTR [edi+1364]
	mov edx, DWORD PTR [edi+1580]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1580], eax
	mov eax, DWORD PTR [edi+1368]
	mov edx, DWORD PTR [edi+1584]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1584], eax
	mov eax, DWORD PTR [edi+1372]
	mov edx, DWORD PTR [edi+1588]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1588], eax
	mov eax, DWORD PTR [edi+1376]
	mov edx, DWORD PTR [edi+1592]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1592], eax
	mov eax, DWORD PTR [edi+1380]
	mov edx, DWORD PTR [edi+1596]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1596], eax
	mov eax, DWORD PTR [edi+1384]
	mov edx, DWORD PTR [edi+1600]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1600], eax
	mov eax, DWORD PTR [edi+1388]
	mov edx, DWORD PTR [edi+1604]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1604], eax
	mov eax, DWORD PTR [edi+1392]
	mov edx, DWORD PTR [edi+1608]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1608], eax
	mov eax, DWORD PTR [edi+1396]
	mov edx, DWORD PTR [edi+1612]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1612], eax
	mov eax, DWORD PTR [edi+1400]
	mov edx, DWORD PTR [edi+1616]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1616], eax
	mov eax, DWORD PTR [edi+1404]
	mov edx, DWORD PTR [edi+1620]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1620], eax
	mov eax, DWORD PTR [edi+1408]
	mov edx, DWORD PTR [edi+1624]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1624], eax
	mov eax, DWORD PTR [edi+1412]
	mov edx, DWORD PTR [edi+1628]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1628], eax
	mov eax, DWORD PTR [edi+1416]
	mov edx, DWORD PTR [edi+1632]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1632], eax
	mov eax, DWORD PTR [edi+1420]
	mov edx, DWORD PTR [edi+1636]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1636], eax
	mov eax, DWORD PTR [edi+1424]
	mov edx, DWORD PTR [edi+1640]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1640], eax
	mov eax, DWORD PTR [edi+1428]
	mov edx, DWORD PTR [edi+1644]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1644], eax
	mov eax, 1504
	mov ecx, 1072
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1576
	mov ecx, 1144
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1216
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1072
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1576
	mov ecx, 1504
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 1936
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1720
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 1936
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1072
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1504
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2080
	mov ecx, 2008
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1720
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2080
	mov ecx, 2008
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1144
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1648
	mov ecx, 1576
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1288
	mov ecx, 2080
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1792
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1288
	mov ecx, 2080
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 496
	mov edx, 1432
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 568
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1288
	mov edx, 1432
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1792
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1792
	mov edx, 1432
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1288
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1720
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 496
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 568
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1720
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 496
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 2008
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 1792
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1360
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 2080
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1288
	mov ecx, 1936
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1288
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1936
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 2080
	mov edx, 1432
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1432
	mov edx, 1432
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1328]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1332]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+1336]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+1340]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+1344]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+1348]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+1352]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+1356]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1360]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+1364]
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [edi+1368]
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [edi+1372]
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [edi+1376]
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [edi+1380]
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [edi+1384]
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [edi+1388]
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [edi+1392]
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [edi+1396]
	mov DWORD PTR [edi+1180], eax
	mov eax, DWORD PTR [edi+1400]
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [edi+1404]
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [edi+1408]
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [edi+1412]
	mov DWORD PTR [edi+1196], eax
	mov eax, DWORD PTR [edi+1416]
	mov DWORD PTR [edi+1200], eax
	mov eax, DWORD PTR [edi+1420]
	mov DWORD PTR [edi+1204], eax
	mov eax, DWORD PTR [edi+1424]
	mov DWORD PTR [edi+1208], eax
	mov eax, DWORD PTR [edi+1428]
	mov DWORD PTR [edi+1212], eax
	mov eax, DWORD PTR [edi+1432]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [edi+1436]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [edi+1440]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+1444]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+1448]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+1452]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+1472]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+1476]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [edi+1480]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [edi+1484]
	mov DWORD PTR [edi+1268], eax
	mov eax, DWORD PTR [edi+1488]
	mov DWORD PTR [edi+1272], eax
	mov eax, DWORD PTR [edi+1492]
	mov DWORD PTR [edi+1276], eax
	mov eax, DWORD PTR [edi+1496]
	mov DWORD PTR [edi+1280], eax
	mov eax, DWORD PTR [edi+1500]
	mov DWORD PTR [edi+1284], eax
	test esi, esi
	jne 21b
	ret
	.p2align 6
