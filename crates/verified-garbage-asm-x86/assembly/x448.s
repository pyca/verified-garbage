// The functions of `src/x448.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x448:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [esi+1]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+64], eax
	mov DWORD PTR [edi+448], eax
	movzx eax, BYTE PTR [esi+2]
	movzx edx, BYTE PTR [esi+3]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+68], eax
	mov DWORD PTR [edi+452], eax
	movzx eax, BYTE PTR [esi+4]
	movzx edx, BYTE PTR [esi+5]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+72], eax
	mov DWORD PTR [edi+456], eax
	movzx eax, BYTE PTR [esi+6]
	movzx edx, BYTE PTR [esi+7]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+76], eax
	mov DWORD PTR [edi+460], eax
	movzx eax, BYTE PTR [esi+8]
	movzx edx, BYTE PTR [esi+9]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+80], eax
	mov DWORD PTR [edi+464], eax
	movzx eax, BYTE PTR [esi+10]
	movzx edx, BYTE PTR [esi+11]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+84], eax
	mov DWORD PTR [edi+468], eax
	movzx eax, BYTE PTR [esi+12]
	movzx edx, BYTE PTR [esi+13]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+88], eax
	mov DWORD PTR [edi+472], eax
	movzx eax, BYTE PTR [esi+14]
	movzx edx, BYTE PTR [esi+15]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+92], eax
	mov DWORD PTR [edi+476], eax
	movzx eax, BYTE PTR [esi+16]
	movzx edx, BYTE PTR [esi+17]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+96], eax
	mov DWORD PTR [edi+480], eax
	movzx eax, BYTE PTR [esi+18]
	movzx edx, BYTE PTR [esi+19]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+100], eax
	mov DWORD PTR [edi+484], eax
	movzx eax, BYTE PTR [esi+20]
	movzx edx, BYTE PTR [esi+21]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+104], eax
	mov DWORD PTR [edi+488], eax
	movzx eax, BYTE PTR [esi+22]
	movzx edx, BYTE PTR [esi+23]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+108], eax
	mov DWORD PTR [edi+492], eax
	movzx eax, BYTE PTR [esi+24]
	movzx edx, BYTE PTR [esi+25]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+112], eax
	mov DWORD PTR [edi+496], eax
	movzx eax, BYTE PTR [esi+26]
	movzx edx, BYTE PTR [esi+27]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+116], eax
	mov DWORD PTR [edi+500], eax
	movzx eax, BYTE PTR [esi+28]
	movzx edx, BYTE PTR [esi+29]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+120], eax
	mov DWORD PTR [edi+504], eax
	movzx eax, BYTE PTR [esi+30]
	movzx edx, BYTE PTR [esi+31]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+124], eax
	mov DWORD PTR [edi+508], eax
	movzx eax, BYTE PTR [esi+32]
	movzx edx, BYTE PTR [esi+33]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+128], eax
	mov DWORD PTR [edi+512], eax
	movzx eax, BYTE PTR [esi+34]
	movzx edx, BYTE PTR [esi+35]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+132], eax
	mov DWORD PTR [edi+516], eax
	movzx eax, BYTE PTR [esi+36]
	movzx edx, BYTE PTR [esi+37]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+136], eax
	mov DWORD PTR [edi+520], eax
	movzx eax, BYTE PTR [esi+38]
	movzx edx, BYTE PTR [esi+39]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+140], eax
	mov DWORD PTR [edi+524], eax
	movzx eax, BYTE PTR [esi+40]
	movzx edx, BYTE PTR [esi+41]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+144], eax
	mov DWORD PTR [edi+528], eax
	movzx eax, BYTE PTR [esi+42]
	movzx edx, BYTE PTR [esi+43]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+148], eax
	mov DWORD PTR [edi+532], eax
	movzx eax, BYTE PTR [esi+44]
	movzx edx, BYTE PTR [esi+45]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+152], eax
	mov DWORD PTR [edi+536], eax
	movzx eax, BYTE PTR [esi+46]
	movzx edx, BYTE PTR [esi+47]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+156], eax
	mov DWORD PTR [edi+540], eax
	movzx eax, BYTE PTR [esi+48]
	movzx edx, BYTE PTR [esi+49]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+160], eax
	mov DWORD PTR [edi+544], eax
	movzx eax, BYTE PTR [esi+50]
	movzx edx, BYTE PTR [esi+51]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+164], eax
	mov DWORD PTR [edi+548], eax
	movzx eax, BYTE PTR [esi+52]
	movzx edx, BYTE PTR [esi+53]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+168], eax
	mov DWORD PTR [edi+552], eax
	movzx eax, BYTE PTR [esi+54]
	movzx edx, BYTE PTR [esi+55]
	ror edx, 24
	add eax, edx
	mov DWORD PTR [edi+172], eax
	mov DWORD PTR [edi+556], eax
	xor eax, eax
	mov DWORD PTR [edi+192], eax
	mov DWORD PTR [edi+196], eax
	mov DWORD PTR [edi+200], eax
	mov DWORD PTR [edi+204], eax
	mov DWORD PTR [edi+208], eax
	mov DWORD PTR [edi+212], eax
	mov DWORD PTR [edi+216], eax
	mov DWORD PTR [edi+220], eax
	mov DWORD PTR [edi+224], eax
	mov DWORD PTR [edi+228], eax
	mov DWORD PTR [edi+232], eax
	mov DWORD PTR [edi+236], eax
	mov DWORD PTR [edi+240], eax
	mov DWORD PTR [edi+244], eax
	mov DWORD PTR [edi+248], eax
	mov DWORD PTR [edi+252], eax
	mov DWORD PTR [edi+256], eax
	mov DWORD PTR [edi+260], eax
	mov DWORD PTR [edi+264], eax
	mov DWORD PTR [edi+268], eax
	mov DWORD PTR [edi+272], eax
	mov DWORD PTR [edi+276], eax
	mov DWORD PTR [edi+280], eax
	mov DWORD PTR [edi+284], eax
	mov DWORD PTR [edi+288], eax
	mov DWORD PTR [edi+292], eax
	mov DWORD PTR [edi+296], eax
	mov DWORD PTR [edi+300], eax
	mov DWORD PTR [edi+304], eax
	mov DWORD PTR [edi+308], eax
	mov DWORD PTR [edi+312], eax
	mov DWORD PTR [edi+316], eax
	mov DWORD PTR [edi+320], eax
	mov DWORD PTR [edi+324], eax
	mov DWORD PTR [edi+328], eax
	mov DWORD PTR [edi+332], eax
	mov DWORD PTR [edi+336], eax
	mov DWORD PTR [edi+340], eax
	mov DWORD PTR [edi+344], eax
	mov DWORD PTR [edi+348], eax
	mov DWORD PTR [edi+352], eax
	mov DWORD PTR [edi+356], eax
	mov DWORD PTR [edi+360], eax
	mov DWORD PTR [edi+364], eax
	mov DWORD PTR [edi+368], eax
	mov DWORD PTR [edi+372], eax
	mov DWORD PTR [edi+376], eax
	mov DWORD PTR [edi+380], eax
	mov DWORD PTR [edi+384], eax
	mov DWORD PTR [edi+388], eax
	mov DWORD PTR [edi+392], eax
	mov DWORD PTR [edi+396], eax
	mov DWORD PTR [edi+400], eax
	mov DWORD PTR [edi+404], eax
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+412], eax
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+420], eax
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+428], eax
	mov DWORD PTR [edi+432], eax
	mov DWORD PTR [edi+436], eax
	mov DWORD PTR [edi+440], eax
	mov DWORD PTR [edi+444], eax
	mov DWORD PTR [edi+576], eax
	mov DWORD PTR [edi+580], eax
	mov DWORD PTR [edi+584], eax
	mov DWORD PTR [edi+588], eax
	mov DWORD PTR [edi+592], eax
	mov DWORD PTR [edi+596], eax
	mov DWORD PTR [edi+600], eax
	mov DWORD PTR [edi+604], eax
	mov DWORD PTR [edi+608], eax
	mov DWORD PTR [edi+612], eax
	mov DWORD PTR [edi+616], eax
	mov DWORD PTR [edi+620], eax
	mov DWORD PTR [edi+624], eax
	mov DWORD PTR [edi+628], eax
	mov DWORD PTR [edi+632], eax
	mov DWORD PTR [edi+636], eax
	mov DWORD PTR [edi+640], eax
	mov DWORD PTR [edi+644], eax
	mov DWORD PTR [edi+648], eax
	mov DWORD PTR [edi+652], eax
	mov DWORD PTR [edi+656], eax
	mov DWORD PTR [edi+660], eax
	mov DWORD PTR [edi+664], eax
	mov DWORD PTR [edi+668], eax
	mov DWORD PTR [edi+672], eax
	mov DWORD PTR [edi+676], eax
	mov DWORD PTR [edi+680], eax
	mov DWORD PTR [edi+684], eax
	mov DWORD PTR [edi+688], eax
	mov DWORD PTR [edi+692], eax
	mov DWORD PTR [edi+696], eax
	mov DWORD PTR [edi+700], eax
	mov DWORD PTR [edi+704], eax
	mov DWORD PTR [edi+708], eax
	mov DWORD PTR [edi+712], eax
	mov DWORD PTR [edi+716], eax
	mov DWORD PTR [edi+720], eax
	mov DWORD PTR [edi+724], eax
	mov DWORD PTR [edi+728], eax
	mov DWORD PTR [edi+732], eax
	mov DWORD PTR [edi+736], eax
	mov DWORD PTR [edi+740], eax
	mov DWORD PTR [edi+744], eax
	mov DWORD PTR [edi+748], eax
	mov DWORD PTR [edi+752], eax
	mov DWORD PTR [edi+756], eax
	mov DWORD PTR [edi+760], eax
	mov DWORD PTR [edi+764], eax
	mov DWORD PTR [edi+768], eax
	mov DWORD PTR [edi+772], eax
	mov DWORD PTR [edi+776], eax
	mov DWORD PTR [edi+780], eax
	mov DWORD PTR [edi+784], eax
	mov DWORD PTR [edi+788], eax
	mov DWORD PTR [edi+792], eax
	mov DWORD PTR [edi+796], eax
	mov DWORD PTR [edi+800], eax
	mov DWORD PTR [edi+804], eax
	mov DWORD PTR [edi+808], eax
	mov DWORD PTR [edi+812], eax
	mov DWORD PTR [edi+816], eax
	mov DWORD PTR [edi+820], eax
	mov DWORD PTR [edi+824], eax
	mov DWORD PTR [edi+828], eax
	mov DWORD PTR [edi+832], eax
	mov DWORD PTR [edi+836], eax
	mov DWORD PTR [edi+840], eax
	mov DWORD PTR [edi+844], eax
	mov DWORD PTR [edi+848], eax
	mov DWORD PTR [edi+852], eax
	mov DWORD PTR [edi+856], eax
	mov DWORD PTR [edi+860], eax
	mov DWORD PTR [edi+864], eax
	mov DWORD PTR [edi+868], eax
	mov DWORD PTR [edi+872], eax
	mov DWORD PTR [edi+876], eax
	mov DWORD PTR [edi+880], eax
	mov DWORD PTR [edi+884], eax
	mov DWORD PTR [edi+888], eax
	mov DWORD PTR [edi+892], eax
	mov DWORD PTR [edi+896], eax
	mov DWORD PTR [edi+900], eax
	mov DWORD PTR [edi+904], eax
	mov DWORD PTR [edi+908], eax
	mov DWORD PTR [edi+912], eax
	mov DWORD PTR [edi+916], eax
	mov DWORD PTR [edi+920], eax
	mov DWORD PTR [edi+924], eax
	mov DWORD PTR [edi+928], eax
	mov DWORD PTR [edi+932], eax
	mov DWORD PTR [edi+936], eax
	mov DWORD PTR [edi+940], eax
	mov DWORD PTR [edi+944], eax
	mov DWORD PTR [edi+948], eax
	mov DWORD PTR [edi+952], eax
	mov DWORD PTR [edi+956], eax
	mov DWORD PTR [edi+960], eax
	mov DWORD PTR [edi+964], eax
	mov DWORD PTR [edi+968], eax
	mov DWORD PTR [edi+972], eax
	mov DWORD PTR [edi+976], eax
	mov DWORD PTR [edi+980], eax
	mov DWORD PTR [edi+984], eax
	mov DWORD PTR [edi+988], eax
	mov DWORD PTR [edi+992], eax
	mov DWORD PTR [edi+996], eax
	mov DWORD PTR [edi+1000], eax
	mov DWORD PTR [edi+1004], eax
	mov DWORD PTR [edi+1008], eax
	mov DWORD PTR [edi+1012], eax
	mov DWORD PTR [edi+1016], eax
	mov DWORD PTR [edi+1020], eax
	mov DWORD PTR [edi+1024], eax
	mov DWORD PTR [edi+1028], eax
	mov DWORD PTR [edi+1032], eax
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], eax
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], eax
	mov DWORD PTR [edi+1060], eax
	mov DWORD PTR [edi+1064], eax
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], eax
	mov DWORD PTR [edi+1076], eax
	mov DWORD PTR [edi+1080], eax
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], eax
	mov DWORD PTR [edi+1092], eax
	mov DWORD PTR [edi+1096], eax
	mov DWORD PTR [edi+1100], eax
	mov DWORD PTR [edi+1104], eax
	mov DWORD PTR [edi+1108], eax
	mov DWORD PTR [edi+1112], eax
	mov DWORD PTR [edi+1116], eax
	mov DWORD PTR [edi+1120], eax
	mov DWORD PTR [edi+1124], eax
	mov DWORD PTR [edi+1128], eax
	mov DWORD PTR [edi+1132], eax
	mov DWORD PTR [edi+1136], eax
	mov DWORD PTR [edi+1140], eax
	mov DWORD PTR [edi+1144], eax
	mov DWORD PTR [edi+1148], eax
	mov DWORD PTR [edi+1152], eax
	mov DWORD PTR [edi+1156], eax
	mov DWORD PTR [edi+1160], eax
	mov DWORD PTR [edi+1164], eax
	mov DWORD PTR [edi+1168], eax
	mov DWORD PTR [edi+1172], eax
	mov DWORD PTR [edi+1176], eax
	mov DWORD PTR [edi+1180], eax
	mov DWORD PTR [edi+1184], eax
	mov DWORD PTR [edi+1188], eax
	mov DWORD PTR [edi+1192], eax
	mov DWORD PTR [edi+1196], eax
	mov DWORD PTR [edi+1200], eax
	mov DWORD PTR [edi+1204], eax
	mov DWORD PTR [edi+1208], eax
	mov DWORD PTR [edi+1212], eax
	mov DWORD PTR [edi+1216], eax
	mov DWORD PTR [edi+1220], eax
	mov DWORD PTR [edi+1224], eax
	mov DWORD PTR [edi+1228], eax
	mov DWORD PTR [edi+1232], eax
	mov DWORD PTR [edi+1236], eax
	mov DWORD PTR [edi+1240], eax
	mov DWORD PTR [edi+1244], eax
	mov DWORD PTR [edi+1248], eax
	mov DWORD PTR [edi+1252], eax
	mov DWORD PTR [edi+1256], eax
	mov DWORD PTR [edi+1260], eax
	mov DWORD PTR [edi+1264], eax
	mov DWORD PTR [edi+1268], eax
	mov DWORD PTR [edi+1272], eax
	mov DWORD PTR [edi+1276], eax
	mov DWORD PTR [edi+1280], eax
	mov DWORD PTR [edi+1284], eax
	mov DWORD PTR [edi+1288], eax
	mov DWORD PTR [edi+1292], eax
	mov DWORD PTR [edi+1296], eax
	mov DWORD PTR [edi+1300], eax
	mov DWORD PTR [edi+1304], eax
	mov DWORD PTR [edi+1308], eax
	mov DWORD PTR [edi+1312], eax
	mov DWORD PTR [edi+1316], eax
	mov DWORD PTR [edi+1320], eax
	mov DWORD PTR [edi+1324], eax
	mov DWORD PTR [edi+1328], eax
	mov DWORD PTR [edi+1332], eax
	mov DWORD PTR [edi+1336], eax
	mov DWORD PTR [edi+1340], eax
	mov DWORD PTR [edi+1344], eax
	mov DWORD PTR [edi+1348], eax
	mov DWORD PTR [edi+1352], eax
	mov DWORD PTR [edi+1356], eax
	mov DWORD PTR [edi+1360], eax
	mov DWORD PTR [edi+1364], eax
	mov DWORD PTR [edi+1368], eax
	mov DWORD PTR [edi+1372], eax
	mov DWORD PTR [edi+1376], eax
	mov DWORD PTR [edi+1380], eax
	mov DWORD PTR [edi+1384], eax
	mov DWORD PTR [edi+1388], eax
	mov DWORD PTR [edi+1392], eax
	mov DWORD PTR [edi+1396], eax
	mov DWORD PTR [edi+1400], eax
	mov DWORD PTR [edi+1404], eax
	mov DWORD PTR [edi+1408], eax
	mov DWORD PTR [edi+1412], eax
	mov DWORD PTR [edi+1416], eax
	mov DWORD PTR [edi+1420], eax
	mov DWORD PTR [edi+1424], eax
	mov DWORD PTR [edi+1428], eax
	mov DWORD PTR [edi+1432], eax
	mov DWORD PTR [edi+1436], eax
	mov DWORD PTR [edi+1440], eax
	mov DWORD PTR [edi+1444], eax
	mov DWORD PTR [edi+1448], eax
	mov DWORD PTR [edi+1452], eax
	mov DWORD PTR [edi+1456], eax
	mov DWORD PTR [edi+1460], eax
	mov DWORD PTR [edi+1464], eax
	mov DWORD PTR [edi+1468], eax
	mov DWORD PTR [edi+1472], eax
	mov DWORD PTR [edi+1476], eax
	mov DWORD PTR [edi+1480], eax
	mov DWORD PTR [edi+1484], eax
	mov DWORD PTR [edi+1488], eax
	mov DWORD PTR [edi+1492], eax
	mov DWORD PTR [edi+1496], eax
	mov DWORD PTR [edi+1500], eax
	mov DWORD PTR [edi+1504], eax
	mov DWORD PTR [edi+1508], eax
	mov DWORD PTR [edi+1512], eax
	mov DWORD PTR [edi+1516], eax
	mov DWORD PTR [edi+1520], eax
	mov DWORD PTR [edi+1524], eax
	mov DWORD PTR [edi+1528], eax
	mov DWORD PTR [edi+1532], eax
	mov DWORD PTR [edi+1536], eax
	mov DWORD PTR [edi+1540], eax
	mov DWORD PTR [edi+1544], eax
	mov DWORD PTR [edi+1548], eax
	mov DWORD PTR [edi+1552], eax
	mov DWORD PTR [edi+1556], eax
	mov DWORD PTR [edi+1560], eax
	mov DWORD PTR [edi+1564], eax
	mov DWORD PTR [edi+1568], eax
	mov DWORD PTR [edi+1572], eax
	mov DWORD PTR [edi+1576], eax
	mov DWORD PTR [edi+1580], eax
	mov DWORD PTR [edi+1584], eax
	mov DWORD PTR [edi+1588], eax
	mov DWORD PTR [edi+1592], eax
	mov DWORD PTR [edi+1596], eax
	mov DWORD PTR [edi+1600], eax
	mov DWORD PTR [edi+1604], eax
	mov DWORD PTR [edi+1608], eax
	mov DWORD PTR [edi+1612], eax
	mov DWORD PTR [edi+1616], eax
	mov DWORD PTR [edi+1620], eax
	mov DWORD PTR [edi+1624], eax
	mov DWORD PTR [edi+1628], eax
	mov DWORD PTR [edi+1632], eax
	mov DWORD PTR [edi+1636], eax
	mov DWORD PTR [edi+1640], eax
	mov DWORD PTR [edi+1644], eax
	mov DWORD PTR [edi+1648], eax
	mov DWORD PTR [edi+1652], eax
	mov DWORD PTR [edi+1656], eax
	mov DWORD PTR [edi+1660], eax
	mov DWORD PTR [edi+1664], eax
	mov DWORD PTR [edi+1668], eax
	mov DWORD PTR [edi+1672], eax
	mov DWORD PTR [edi+1676], eax
	mov DWORD PTR [edi+1680], eax
	mov DWORD PTR [edi+1684], eax
	mov DWORD PTR [edi+1688], eax
	mov DWORD PTR [edi+1692], eax
	mov DWORD PTR [edi+1696], eax
	mov DWORD PTR [edi+1700], eax
	mov DWORD PTR [edi+1704], eax
	mov DWORD PTR [edi+1708], eax
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
	mov DWORD PTR [edi+1756], eax
	mov DWORD PTR [edi+1760], eax
	mov DWORD PTR [edi+1764], eax
	mov DWORD PTR [edi+1768], eax
	mov DWORD PTR [edi+1772], eax
	mov DWORD PTR [edi+1776], eax
	mov DWORD PTR [edi+1780], eax
	mov DWORD PTR [edi+1784], eax
	mov DWORD PTR [edi+1788], eax
	mov DWORD PTR [edi+1792], eax
	mov DWORD PTR [edi+1796], eax
	mov DWORD PTR [edi+1800], eax
	mov DWORD PTR [edi+1804], eax
	mov DWORD PTR [edi+1808], eax
	mov DWORD PTR [edi+1812], eax
	mov DWORD PTR [edi+1816], eax
	mov DWORD PTR [edi+1820], eax
	mov DWORD PTR [edi+1824], eax
	mov DWORD PTR [edi+1828], eax
	mov DWORD PTR [edi+1832], eax
	mov DWORD PTR [edi+1836], eax
	mov DWORD PTR [edi+1840], eax
	mov DWORD PTR [edi+1844], eax
	mov DWORD PTR [edi+1848], eax
	mov DWORD PTR [edi+1852], eax
	mov DWORD PTR [edi+1856], eax
	mov DWORD PTR [edi+1860], eax
	mov DWORD PTR [edi+1864], eax
	mov DWORD PTR [edi+1868], eax
	mov DWORD PTR [edi+1872], eax
	mov DWORD PTR [edi+1876], eax
	mov DWORD PTR [edi+1880], eax
	mov DWORD PTR [edi+1884], eax
	mov DWORD PTR [edi+1888], eax
	mov DWORD PTR [edi+1892], eax
	mov DWORD PTR [edi+1896], eax
	mov DWORD PTR [edi+1900], eax
	mov DWORD PTR [edi+1904], eax
	mov DWORD PTR [edi+1908], eax
	mov DWORD PTR [edi+1912], eax
	mov DWORD PTR [edi+1916], eax
	mov DWORD PTR [edi+1920], eax
	mov DWORD PTR [edi+1924], eax
	mov DWORD PTR [edi+1928], eax
	mov DWORD PTR [edi+1932], eax
	mov DWORD PTR [edi+1936], eax
	mov DWORD PTR [edi+1940], eax
	mov DWORD PTR [edi+1944], eax
	mov DWORD PTR [edi+1948], eax
	mov DWORD PTR [edi+1952], eax
	mov DWORD PTR [edi+1956], eax
	mov DWORD PTR [edi+1960], eax
	mov DWORD PTR [edi+1964], eax
	mov DWORD PTR [edi+1968], eax
	mov DWORD PTR [edi+1972], eax
	mov DWORD PTR [edi+1976], eax
	mov DWORD PTR [edi+1980], eax
	mov DWORD PTR [edi+1984], eax
	mov DWORD PTR [edi+1988], eax
	mov DWORD PTR [edi+1992], eax
	mov DWORD PTR [edi+1996], eax
	mov DWORD PTR [edi+2000], eax
	mov DWORD PTR [edi+2004], eax
	mov DWORD PTR [edi+2008], eax
	mov DWORD PTR [edi+2012], eax
	mov DWORD PTR [edi+2016], eax
	mov DWORD PTR [edi+2020], eax
	mov DWORD PTR [edi+2024], eax
	mov DWORD PTR [edi+2028], eax
	mov DWORD PTR [edi+2032], eax
	mov DWORD PTR [edi+2036], eax
	mov DWORD PTR [edi+2040], eax
	mov DWORD PTR [edi+2044], eax
	mov DWORD PTR [edi+2048], eax
	mov DWORD PTR [edi+2052], eax
	mov DWORD PTR [edi+2056], eax
	mov DWORD PTR [edi+2060], eax
	mov DWORD PTR [edi+2064], eax
	mov DWORD PTR [edi+2068], eax
	mov DWORD PTR [edi+2072], eax
	mov DWORD PTR [edi+2076], eax
	mov DWORD PTR [edi+2080], eax
	mov DWORD PTR [edi+2084], eax
	mov DWORD PTR [edi+2088], eax
	mov DWORD PTR [edi+2092], eax
	mov DWORD PTR [edi+2096], eax
	mov DWORD PTR [edi+2100], eax
	mov DWORD PTR [edi+2104], eax
	mov DWORD PTR [edi+2108], eax
	mov DWORD PTR [edi+2112], eax
	mov DWORD PTR [edi+2116], eax
	mov DWORD PTR [edi+2120], eax
	mov DWORD PTR [edi+2124], eax
	mov DWORD PTR [edi+2128], eax
	mov DWORD PTR [edi+2132], eax
	mov DWORD PTR [edi+2136], eax
	mov DWORD PTR [edi+2140], eax
	mov DWORD PTR [edi+2144], eax
	mov DWORD PTR [edi+2148], eax
	mov DWORD PTR [edi+2152], eax
	mov DWORD PTR [edi+2156], eax
	mov DWORD PTR [edi+2160], eax
	mov DWORD PTR [edi+2164], eax
	mov DWORD PTR [edi+2168], eax
	mov DWORD PTR [edi+2172], eax
	mov DWORD PTR [edi+2176], eax
	mov DWORD PTR [edi+2180], eax
	mov DWORD PTR [edi+2184], eax
	mov DWORD PTR [edi+2188], eax
	mov DWORD PTR [edi+2192], eax
	mov DWORD PTR [edi+2196], eax
	mov DWORD PTR [edi+2200], eax
	mov DWORD PTR [edi+2204], eax
	mov DWORD PTR [edi+2208], eax
	mov DWORD PTR [edi+2212], eax
	mov DWORD PTR [edi+2216], eax
	mov DWORD PTR [edi+2220], eax
	mov DWORD PTR [edi+2224], eax
	mov DWORD PTR [edi+2228], eax
	mov DWORD PTR [edi+2232], eax
	mov DWORD PTR [edi+2236], eax
	mov DWORD PTR [edi+2240], eax
	mov DWORD PTR [edi+2244], eax
	mov DWORD PTR [edi+2248], eax
	mov DWORD PTR [edi+2252], eax
	mov DWORD PTR [edi+2256], eax
	mov DWORD PTR [edi+2260], eax
	mov DWORD PTR [edi+2264], eax
	mov DWORD PTR [edi+2268], eax
	mov DWORD PTR [edi+2272], eax
	mov DWORD PTR [edi+2276], eax
	mov DWORD PTR [edi+2280], eax
	mov DWORD PTR [edi+2284], eax
	mov DWORD PTR [edi+2288], eax
	mov DWORD PTR [edi+2292], eax
	mov DWORD PTR [edi+2296], eax
	mov DWORD PTR [edi+2300], eax
	mov DWORD PTR [edi+2304], eax
	mov DWORD PTR [edi+2308], eax
	mov DWORD PTR [edi+2312], eax
	mov DWORD PTR [edi+2316], eax
	mov DWORD PTR [edi+2320], eax
	mov DWORD PTR [edi+2324], eax
	mov DWORD PTR [edi+2328], eax
	mov DWORD PTR [edi+2332], eax
	mov DWORD PTR [edi+2336], eax
	mov DWORD PTR [edi+2340], eax
	mov DWORD PTR [edi+2344], eax
	mov DWORD PTR [edi+2348], eax
	mov DWORD PTR [edi+2352], eax
	mov DWORD PTR [edi+2356], eax
	mov DWORD PTR [edi+2360], eax
	mov DWORD PTR [edi+2364], eax
	mov DWORD PTR [edi+2368], eax
	mov DWORD PTR [edi+2372], eax
	mov DWORD PTR [edi+2376], eax
	mov DWORD PTR [edi+2380], eax
	mov DWORD PTR [edi+2384], eax
	mov DWORD PTR [edi+2388], eax
	mov DWORD PTR [edi+2392], eax
	mov DWORD PTR [edi+2396], eax
	mov DWORD PTR [edi+2400], eax
	mov DWORD PTR [edi+2404], eax
	mov DWORD PTR [edi+2408], eax
	mov DWORD PTR [edi+2412], eax
	mov DWORD PTR [edi+2416], eax
	mov DWORD PTR [edi+2420], eax
	mov DWORD PTR [edi+2424], eax
	mov DWORD PTR [edi+2428], eax
	mov DWORD PTR [edi+2432], eax
	mov DWORD PTR [edi+2436], eax
	mov DWORD PTR [edi+2440], eax
	mov DWORD PTR [edi+2444], eax
	mov DWORD PTR [edi+2448], eax
	mov DWORD PTR [edi+2452], eax
	mov DWORD PTR [edi+2456], eax
	mov DWORD PTR [edi+2460], eax
	mov DWORD PTR [edi+2464], eax
	mov DWORD PTR [edi+2468], eax
	mov DWORD PTR [edi+2472], eax
	mov DWORD PTR [edi+2476], eax
	mov DWORD PTR [edi+2480], eax
	mov DWORD PTR [edi+2484], eax
	mov DWORD PTR [edi+2488], eax
	mov DWORD PTR [edi+2492], eax
	mov DWORD PTR [edi+2496], eax
	mov DWORD PTR [edi+2500], eax
	mov DWORD PTR [edi+2504], eax
	mov DWORD PTR [edi+2508], eax
	mov DWORD PTR [edi+2512], eax
	mov DWORD PTR [edi+2516], eax
	mov DWORD PTR [edi+2520], eax
	mov DWORD PTR [edi+2524], eax
	mov DWORD PTR [edi+2528], eax
	mov DWORD PTR [edi+2532], eax
	mov DWORD PTR [edi+2536], eax
	mov DWORD PTR [edi+2540], eax
	mov DWORD PTR [edi+2544], eax
	mov DWORD PTR [edi+2548], eax
	mov DWORD PTR [edi+2552], eax
	mov DWORD PTR [edi+2556], eax
	mov DWORD PTR [edi+2560], eax
	mov DWORD PTR [edi+2564], eax
	mov DWORD PTR [edi+2568], eax
	mov DWORD PTR [edi+2572], eax
	mov DWORD PTR [edi+2576], eax
	mov DWORD PTR [edi+2580], eax
	mov DWORD PTR [edi+2584], eax
	mov DWORD PTR [edi+2588], eax
	mov DWORD PTR [edi+2592], eax
	mov DWORD PTR [edi+2596], eax
	mov DWORD PTR [edi+2600], eax
	mov DWORD PTR [edi+2604], eax
	mov DWORD PTR [edi+2608], eax
	mov DWORD PTR [edi+2612], eax
	mov DWORD PTR [edi+2616], eax
	mov DWORD PTR [edi+2620], eax
	mov DWORD PTR [edi+2624], eax
	mov DWORD PTR [edi+2628], eax
	mov DWORD PTR [edi+2632], eax
	mov DWORD PTR [edi+2636], eax
	mov DWORD PTR [edi+2640], eax
	mov DWORD PTR [edi+2644], eax
	mov DWORD PTR [edi+2648], eax
	mov DWORD PTR [edi+2652], eax
	mov DWORD PTR [edi+2656], eax
	mov DWORD PTR [edi+2660], eax
	mov DWORD PTR [edi+2664], eax
	mov DWORD PTR [edi+2668], eax
	mov DWORD PTR [edi+2672], eax
	mov DWORD PTR [edi+2676], eax
	mov DWORD PTR [edi+2680], eax
	mov DWORD PTR [edi+2684], eax
	mov DWORD PTR [edi+2688], eax
	mov DWORD PTR [edi+2692], eax
	mov DWORD PTR [edi+2696], eax
	mov DWORD PTR [edi+2700], eax
	mov DWORD PTR [edi+2704], eax
	mov DWORD PTR [edi+2708], eax
	mov DWORD PTR [edi+2712], eax
	mov DWORD PTR [edi+2716], eax
	mov DWORD PTR [edi+2720], eax
	mov DWORD PTR [edi+2724], eax
	mov DWORD PTR [edi+2728], eax
	mov DWORD PTR [edi+2732], eax
	mov DWORD PTR [edi+2736], eax
	mov DWORD PTR [edi+2740], eax
	mov DWORD PTR [edi+2744], eax
	mov DWORD PTR [edi+2748], eax
	mov DWORD PTR [edi+2752], eax
	mov DWORD PTR [edi+2756], eax
	mov DWORD PTR [edi+2760], eax
	mov DWORD PTR [edi+2764], eax
	mov DWORD PTR [edi+2768], eax
	mov DWORD PTR [edi+2772], eax
	mov DWORD PTR [edi+2776], eax
	mov DWORD PTR [edi+2780], eax
	mov DWORD PTR [edi+2784], eax
	mov DWORD PTR [edi+2788], eax
	mov DWORD PTR [edi+2792], eax
	mov DWORD PTR [edi+2796], eax
	mov DWORD PTR [edi+2800], eax
	mov DWORD PTR [edi+2804], eax
	mov DWORD PTR [edi+2808], eax
	mov DWORD PTR [edi+2812], eax
	mov DWORD PTR [edi+2816], eax
	mov DWORD PTR [edi+2820], eax
	mov DWORD PTR [edi+2824], eax
	mov DWORD PTR [edi+2828], eax
	mov DWORD PTR [edi+2832], eax
	mov DWORD PTR [edi+2836], eax
	mov DWORD PTR [edi+2840], eax
	mov DWORD PTR [edi+2844], eax
	mov DWORD PTR [edi+2848], eax
	mov DWORD PTR [edi+2852], eax
	mov DWORD PTR [edi+2856], eax
	mov DWORD PTR [edi+2860], eax
	mov DWORD PTR [edi+2864], eax
	mov DWORD PTR [edi+2868], eax
	mov DWORD PTR [edi+2872], eax
	mov DWORD PTR [edi+2876], eax
	mov DWORD PTR [edi+32], eax
	mov eax, 1
	mov DWORD PTR [edi+192], eax
	mov DWORD PTR [edi+576], eax
	mov esi, DWORD PTR [esp+8]
	mov ebp, edi
	mov ecx, 56
20:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebp+3072], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebp+3073], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebp+3074], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebp+3075], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebp+3076], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebp+3077], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebp+3078], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebp+3079], dl
	add esi, 1
	add ebp, 8
	sub ecx, 1
	jne 20b
	mov edx, 0
	mov BYTE PTR [edi+3072], dl
	mov BYTE PTR [edi+3073], dl
	mov edx, 1
	mov BYTE PTR [edi+3519], dl
	mov esi, 448
21:
	sub esi, 1
	mov ebp, edi
	add ebp, esi
	movzx eax, BYTE PTR [ebp+3072]
	mov ecx, DWORD PTR [edi+32]
	xor ecx, eax
	mov DWORD PTR [edi+32], eax
	mov ebx, 0
	sub ebx, ecx
	mov eax, DWORD PTR [edi+192]
	mov ecx, DWORD PTR [edi+448]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+192], eax
	mov DWORD PTR [edi+448], ecx
	mov eax, DWORD PTR [edi+196]
	mov ecx, DWORD PTR [edi+452]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+196], eax
	mov DWORD PTR [edi+452], ecx
	mov eax, DWORD PTR [edi+200]
	mov ecx, DWORD PTR [edi+456]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+200], eax
	mov DWORD PTR [edi+456], ecx
	mov eax, DWORD PTR [edi+204]
	mov ecx, DWORD PTR [edi+460]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+204], eax
	mov DWORD PTR [edi+460], ecx
	mov eax, DWORD PTR [edi+208]
	mov ecx, DWORD PTR [edi+464]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+208], eax
	mov DWORD PTR [edi+464], ecx
	mov eax, DWORD PTR [edi+212]
	mov ecx, DWORD PTR [edi+468]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+212], eax
	mov DWORD PTR [edi+468], ecx
	mov eax, DWORD PTR [edi+216]
	mov ecx, DWORD PTR [edi+472]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+216], eax
	mov DWORD PTR [edi+472], ecx
	mov eax, DWORD PTR [edi+220]
	mov ecx, DWORD PTR [edi+476]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+220], eax
	mov DWORD PTR [edi+476], ecx
	mov eax, DWORD PTR [edi+224]
	mov ecx, DWORD PTR [edi+480]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+224], eax
	mov DWORD PTR [edi+480], ecx
	mov eax, DWORD PTR [edi+228]
	mov ecx, DWORD PTR [edi+484]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+228], eax
	mov DWORD PTR [edi+484], ecx
	mov eax, DWORD PTR [edi+232]
	mov ecx, DWORD PTR [edi+488]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+232], eax
	mov DWORD PTR [edi+488], ecx
	mov eax, DWORD PTR [edi+236]
	mov ecx, DWORD PTR [edi+492]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+236], eax
	mov DWORD PTR [edi+492], ecx
	mov eax, DWORD PTR [edi+240]
	mov ecx, DWORD PTR [edi+496]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+240], eax
	mov DWORD PTR [edi+496], ecx
	mov eax, DWORD PTR [edi+244]
	mov ecx, DWORD PTR [edi+500]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+244], eax
	mov DWORD PTR [edi+500], ecx
	mov eax, DWORD PTR [edi+248]
	mov ecx, DWORD PTR [edi+504]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+248], eax
	mov DWORD PTR [edi+504], ecx
	mov eax, DWORD PTR [edi+252]
	mov ecx, DWORD PTR [edi+508]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+252], eax
	mov DWORD PTR [edi+508], ecx
	mov eax, DWORD PTR [edi+256]
	mov ecx, DWORD PTR [edi+512]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+256], eax
	mov DWORD PTR [edi+512], ecx
	mov eax, DWORD PTR [edi+260]
	mov ecx, DWORD PTR [edi+516]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+260], eax
	mov DWORD PTR [edi+516], ecx
	mov eax, DWORD PTR [edi+264]
	mov ecx, DWORD PTR [edi+520]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+264], eax
	mov DWORD PTR [edi+520], ecx
	mov eax, DWORD PTR [edi+268]
	mov ecx, DWORD PTR [edi+524]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+268], eax
	mov DWORD PTR [edi+524], ecx
	mov eax, DWORD PTR [edi+272]
	mov ecx, DWORD PTR [edi+528]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+272], eax
	mov DWORD PTR [edi+528], ecx
	mov eax, DWORD PTR [edi+276]
	mov ecx, DWORD PTR [edi+532]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+276], eax
	mov DWORD PTR [edi+532], ecx
	mov eax, DWORD PTR [edi+280]
	mov ecx, DWORD PTR [edi+536]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+280], eax
	mov DWORD PTR [edi+536], ecx
	mov eax, DWORD PTR [edi+284]
	mov ecx, DWORD PTR [edi+540]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+284], eax
	mov DWORD PTR [edi+540], ecx
	mov eax, DWORD PTR [edi+288]
	mov ecx, DWORD PTR [edi+544]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+288], eax
	mov DWORD PTR [edi+544], ecx
	mov eax, DWORD PTR [edi+292]
	mov ecx, DWORD PTR [edi+548]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+292], eax
	mov DWORD PTR [edi+548], ecx
	mov eax, DWORD PTR [edi+296]
	mov ecx, DWORD PTR [edi+552]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+296], eax
	mov DWORD PTR [edi+552], ecx
	mov eax, DWORD PTR [edi+300]
	mov ecx, DWORD PTR [edi+556]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+300], eax
	mov DWORD PTR [edi+556], ecx
	mov eax, DWORD PTR [edi+320]
	mov ecx, DWORD PTR [edi+576]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+320], eax
	mov DWORD PTR [edi+576], ecx
	mov eax, DWORD PTR [edi+324]
	mov ecx, DWORD PTR [edi+580]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+324], eax
	mov DWORD PTR [edi+580], ecx
	mov eax, DWORD PTR [edi+328]
	mov ecx, DWORD PTR [edi+584]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+328], eax
	mov DWORD PTR [edi+584], ecx
	mov eax, DWORD PTR [edi+332]
	mov ecx, DWORD PTR [edi+588]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+332], eax
	mov DWORD PTR [edi+588], ecx
	mov eax, DWORD PTR [edi+336]
	mov ecx, DWORD PTR [edi+592]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+336], eax
	mov DWORD PTR [edi+592], ecx
	mov eax, DWORD PTR [edi+340]
	mov ecx, DWORD PTR [edi+596]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+340], eax
	mov DWORD PTR [edi+596], ecx
	mov eax, DWORD PTR [edi+344]
	mov ecx, DWORD PTR [edi+600]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+344], eax
	mov DWORD PTR [edi+600], ecx
	mov eax, DWORD PTR [edi+348]
	mov ecx, DWORD PTR [edi+604]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+348], eax
	mov DWORD PTR [edi+604], ecx
	mov eax, DWORD PTR [edi+352]
	mov ecx, DWORD PTR [edi+608]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+352], eax
	mov DWORD PTR [edi+608], ecx
	mov eax, DWORD PTR [edi+356]
	mov ecx, DWORD PTR [edi+612]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+356], eax
	mov DWORD PTR [edi+612], ecx
	mov eax, DWORD PTR [edi+360]
	mov ecx, DWORD PTR [edi+616]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+360], eax
	mov DWORD PTR [edi+616], ecx
	mov eax, DWORD PTR [edi+364]
	mov ecx, DWORD PTR [edi+620]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+364], eax
	mov DWORD PTR [edi+620], ecx
	mov eax, DWORD PTR [edi+368]
	mov ecx, DWORD PTR [edi+624]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+368], eax
	mov DWORD PTR [edi+624], ecx
	mov eax, DWORD PTR [edi+372]
	mov ecx, DWORD PTR [edi+628]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+372], eax
	mov DWORD PTR [edi+628], ecx
	mov eax, DWORD PTR [edi+376]
	mov ecx, DWORD PTR [edi+632]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+376], eax
	mov DWORD PTR [edi+632], ecx
	mov eax, DWORD PTR [edi+380]
	mov ecx, DWORD PTR [edi+636]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+380], eax
	mov DWORD PTR [edi+636], ecx
	mov eax, DWORD PTR [edi+384]
	mov ecx, DWORD PTR [edi+640]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+384], eax
	mov DWORD PTR [edi+640], ecx
	mov eax, DWORD PTR [edi+388]
	mov ecx, DWORD PTR [edi+644]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+388], eax
	mov DWORD PTR [edi+644], ecx
	mov eax, DWORD PTR [edi+392]
	mov ecx, DWORD PTR [edi+648]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+392], eax
	mov DWORD PTR [edi+648], ecx
	mov eax, DWORD PTR [edi+396]
	mov ecx, DWORD PTR [edi+652]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+396], eax
	mov DWORD PTR [edi+652], ecx
	mov eax, DWORD PTR [edi+400]
	mov ecx, DWORD PTR [edi+656]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+400], eax
	mov DWORD PTR [edi+656], ecx
	mov eax, DWORD PTR [edi+404]
	mov ecx, DWORD PTR [edi+660]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+404], eax
	mov DWORD PTR [edi+660], ecx
	mov eax, DWORD PTR [edi+408]
	mov ecx, DWORD PTR [edi+664]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+664], ecx
	mov eax, DWORD PTR [edi+412]
	mov ecx, DWORD PTR [edi+668]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+412], eax
	mov DWORD PTR [edi+668], ecx
	mov eax, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [edi+672]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+672], ecx
	mov eax, DWORD PTR [edi+420]
	mov ecx, DWORD PTR [edi+676]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+420], eax
	mov DWORD PTR [edi+676], ecx
	mov eax, DWORD PTR [edi+424]
	mov ecx, DWORD PTR [edi+680]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+680], ecx
	mov eax, DWORD PTR [edi+428]
	mov ecx, DWORD PTR [edi+684]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+428], eax
	mov DWORD PTR [edi+684], ecx
	mov eax, 704
	mov ecx, 192
	mov edx, 320
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 704
	mov edx, 704
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 192
	mov edx, 320
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 832
	mov edx, 832
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1216
	mov edx, 1344
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 960
	mov ecx, 448
	mov edx, 576
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 448
	mov edx, 576
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1088
	mov edx, 704
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 960
	mov edx, 832
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 1600
	mov edx, 1728
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 448
	mov edx, 448
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 1600
	mov edx, 1728
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 576
	mov edx, 576
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 64
	mov edx, 576
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 192
	mov ecx, 1216
	mov edx, 1344
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 320
	mov ecx, 1472
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul_a24}
	pop eax
	pop eax
	pop eax
	mov eax, 320
	mov ecx, 1216
	mov edx, 320
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 320
	mov ecx, 1472
	mov edx, 320
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	cmp esi, 0
	jne 21b
	mov ecx, DWORD PTR [edi+32]
	mov ebx, 0
	sub ebx, ecx
	mov eax, DWORD PTR [edi+192]
	mov ecx, DWORD PTR [edi+448]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+192], eax
	mov DWORD PTR [edi+448], ecx
	mov eax, DWORD PTR [edi+196]
	mov ecx, DWORD PTR [edi+452]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+196], eax
	mov DWORD PTR [edi+452], ecx
	mov eax, DWORD PTR [edi+200]
	mov ecx, DWORD PTR [edi+456]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+200], eax
	mov DWORD PTR [edi+456], ecx
	mov eax, DWORD PTR [edi+204]
	mov ecx, DWORD PTR [edi+460]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+204], eax
	mov DWORD PTR [edi+460], ecx
	mov eax, DWORD PTR [edi+208]
	mov ecx, DWORD PTR [edi+464]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+208], eax
	mov DWORD PTR [edi+464], ecx
	mov eax, DWORD PTR [edi+212]
	mov ecx, DWORD PTR [edi+468]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+212], eax
	mov DWORD PTR [edi+468], ecx
	mov eax, DWORD PTR [edi+216]
	mov ecx, DWORD PTR [edi+472]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+216], eax
	mov DWORD PTR [edi+472], ecx
	mov eax, DWORD PTR [edi+220]
	mov ecx, DWORD PTR [edi+476]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+220], eax
	mov DWORD PTR [edi+476], ecx
	mov eax, DWORD PTR [edi+224]
	mov ecx, DWORD PTR [edi+480]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+224], eax
	mov DWORD PTR [edi+480], ecx
	mov eax, DWORD PTR [edi+228]
	mov ecx, DWORD PTR [edi+484]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+228], eax
	mov DWORD PTR [edi+484], ecx
	mov eax, DWORD PTR [edi+232]
	mov ecx, DWORD PTR [edi+488]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+232], eax
	mov DWORD PTR [edi+488], ecx
	mov eax, DWORD PTR [edi+236]
	mov ecx, DWORD PTR [edi+492]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+236], eax
	mov DWORD PTR [edi+492], ecx
	mov eax, DWORD PTR [edi+240]
	mov ecx, DWORD PTR [edi+496]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+240], eax
	mov DWORD PTR [edi+496], ecx
	mov eax, DWORD PTR [edi+244]
	mov ecx, DWORD PTR [edi+500]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+244], eax
	mov DWORD PTR [edi+500], ecx
	mov eax, DWORD PTR [edi+248]
	mov ecx, DWORD PTR [edi+504]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+248], eax
	mov DWORD PTR [edi+504], ecx
	mov eax, DWORD PTR [edi+252]
	mov ecx, DWORD PTR [edi+508]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+252], eax
	mov DWORD PTR [edi+508], ecx
	mov eax, DWORD PTR [edi+256]
	mov ecx, DWORD PTR [edi+512]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+256], eax
	mov DWORD PTR [edi+512], ecx
	mov eax, DWORD PTR [edi+260]
	mov ecx, DWORD PTR [edi+516]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+260], eax
	mov DWORD PTR [edi+516], ecx
	mov eax, DWORD PTR [edi+264]
	mov ecx, DWORD PTR [edi+520]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+264], eax
	mov DWORD PTR [edi+520], ecx
	mov eax, DWORD PTR [edi+268]
	mov ecx, DWORD PTR [edi+524]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+268], eax
	mov DWORD PTR [edi+524], ecx
	mov eax, DWORD PTR [edi+272]
	mov ecx, DWORD PTR [edi+528]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+272], eax
	mov DWORD PTR [edi+528], ecx
	mov eax, DWORD PTR [edi+276]
	mov ecx, DWORD PTR [edi+532]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+276], eax
	mov DWORD PTR [edi+532], ecx
	mov eax, DWORD PTR [edi+280]
	mov ecx, DWORD PTR [edi+536]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+280], eax
	mov DWORD PTR [edi+536], ecx
	mov eax, DWORD PTR [edi+284]
	mov ecx, DWORD PTR [edi+540]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+284], eax
	mov DWORD PTR [edi+540], ecx
	mov eax, DWORD PTR [edi+288]
	mov ecx, DWORD PTR [edi+544]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+288], eax
	mov DWORD PTR [edi+544], ecx
	mov eax, DWORD PTR [edi+292]
	mov ecx, DWORD PTR [edi+548]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+292], eax
	mov DWORD PTR [edi+548], ecx
	mov eax, DWORD PTR [edi+296]
	mov ecx, DWORD PTR [edi+552]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+296], eax
	mov DWORD PTR [edi+552], ecx
	mov eax, DWORD PTR [edi+300]
	mov ecx, DWORD PTR [edi+556]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+300], eax
	mov DWORD PTR [edi+556], ecx
	mov eax, DWORD PTR [edi+320]
	mov ecx, DWORD PTR [edi+576]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+320], eax
	mov DWORD PTR [edi+576], ecx
	mov eax, DWORD PTR [edi+324]
	mov ecx, DWORD PTR [edi+580]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+324], eax
	mov DWORD PTR [edi+580], ecx
	mov eax, DWORD PTR [edi+328]
	mov ecx, DWORD PTR [edi+584]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+328], eax
	mov DWORD PTR [edi+584], ecx
	mov eax, DWORD PTR [edi+332]
	mov ecx, DWORD PTR [edi+588]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+332], eax
	mov DWORD PTR [edi+588], ecx
	mov eax, DWORD PTR [edi+336]
	mov ecx, DWORD PTR [edi+592]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+336], eax
	mov DWORD PTR [edi+592], ecx
	mov eax, DWORD PTR [edi+340]
	mov ecx, DWORD PTR [edi+596]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+340], eax
	mov DWORD PTR [edi+596], ecx
	mov eax, DWORD PTR [edi+344]
	mov ecx, DWORD PTR [edi+600]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+344], eax
	mov DWORD PTR [edi+600], ecx
	mov eax, DWORD PTR [edi+348]
	mov ecx, DWORD PTR [edi+604]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+348], eax
	mov DWORD PTR [edi+604], ecx
	mov eax, DWORD PTR [edi+352]
	mov ecx, DWORD PTR [edi+608]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+352], eax
	mov DWORD PTR [edi+608], ecx
	mov eax, DWORD PTR [edi+356]
	mov ecx, DWORD PTR [edi+612]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+356], eax
	mov DWORD PTR [edi+612], ecx
	mov eax, DWORD PTR [edi+360]
	mov ecx, DWORD PTR [edi+616]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+360], eax
	mov DWORD PTR [edi+616], ecx
	mov eax, DWORD PTR [edi+364]
	mov ecx, DWORD PTR [edi+620]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+364], eax
	mov DWORD PTR [edi+620], ecx
	mov eax, DWORD PTR [edi+368]
	mov ecx, DWORD PTR [edi+624]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+368], eax
	mov DWORD PTR [edi+624], ecx
	mov eax, DWORD PTR [edi+372]
	mov ecx, DWORD PTR [edi+628]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+372], eax
	mov DWORD PTR [edi+628], ecx
	mov eax, DWORD PTR [edi+376]
	mov ecx, DWORD PTR [edi+632]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+376], eax
	mov DWORD PTR [edi+632], ecx
	mov eax, DWORD PTR [edi+380]
	mov ecx, DWORD PTR [edi+636]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+380], eax
	mov DWORD PTR [edi+636], ecx
	mov eax, DWORD PTR [edi+384]
	mov ecx, DWORD PTR [edi+640]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+384], eax
	mov DWORD PTR [edi+640], ecx
	mov eax, DWORD PTR [edi+388]
	mov ecx, DWORD PTR [edi+644]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+388], eax
	mov DWORD PTR [edi+644], ecx
	mov eax, DWORD PTR [edi+392]
	mov ecx, DWORD PTR [edi+648]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+392], eax
	mov DWORD PTR [edi+648], ecx
	mov eax, DWORD PTR [edi+396]
	mov ecx, DWORD PTR [edi+652]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+396], eax
	mov DWORD PTR [edi+652], ecx
	mov eax, DWORD PTR [edi+400]
	mov ecx, DWORD PTR [edi+656]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+400], eax
	mov DWORD PTR [edi+656], ecx
	mov eax, DWORD PTR [edi+404]
	mov ecx, DWORD PTR [edi+660]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+404], eax
	mov DWORD PTR [edi+660], ecx
	mov eax, DWORD PTR [edi+408]
	mov ecx, DWORD PTR [edi+664]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+664], ecx
	mov eax, DWORD PTR [edi+412]
	mov ecx, DWORD PTR [edi+668]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+412], eax
	mov DWORD PTR [edi+668], ecx
	mov eax, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [edi+672]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+672], ecx
	mov eax, DWORD PTR [edi+420]
	mov ecx, DWORD PTR [edi+676]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+420], eax
	mov DWORD PTR [edi+676], ecx
	mov eax, DWORD PTR [edi+424]
	mov ecx, DWORD PTR [edi+680]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+680], ecx
	mov eax, DWORD PTR [edi+428]
	mov ecx, DWORD PTR [edi+684]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+428], eax
	mov DWORD PTR [edi+684], ecx
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+1856], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+1860], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+1864], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+1868], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+1872], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+1876], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+1880], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+1884], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+1888], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+1892], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+1896], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+1900], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+1904], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+1908], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+1912], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+1916], eax
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
	mov esi, 1
22:
	mov eax, 1856
	mov ecx, 1856
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 22b
	mov eax, 1856
	mov ecx, 1856
	mov edx, 320
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1856]
	mov DWORD PTR [edi+1984], eax
	mov eax, DWORD PTR [edi+1860]
	mov DWORD PTR [edi+1988], eax
	mov eax, DWORD PTR [edi+1864]
	mov DWORD PTR [edi+1992], eax
	mov eax, DWORD PTR [edi+1868]
	mov DWORD PTR [edi+1996], eax
	mov eax, DWORD PTR [edi+1872]
	mov DWORD PTR [edi+2000], eax
	mov eax, DWORD PTR [edi+1876]
	mov DWORD PTR [edi+2004], eax
	mov eax, DWORD PTR [edi+1880]
	mov DWORD PTR [edi+2008], eax
	mov eax, DWORD PTR [edi+1884]
	mov DWORD PTR [edi+2012], eax
	mov eax, DWORD PTR [edi+1888]
	mov DWORD PTR [edi+2016], eax
	mov eax, DWORD PTR [edi+1892]
	mov DWORD PTR [edi+2020], eax
	mov eax, DWORD PTR [edi+1896]
	mov DWORD PTR [edi+2024], eax
	mov eax, DWORD PTR [edi+1900]
	mov DWORD PTR [edi+2028], eax
	mov eax, DWORD PTR [edi+1904]
	mov DWORD PTR [edi+2032], eax
	mov eax, DWORD PTR [edi+1908]
	mov DWORD PTR [edi+2036], eax
	mov eax, DWORD PTR [edi+1912]
	mov DWORD PTR [edi+2040], eax
	mov eax, DWORD PTR [edi+1916]
	mov DWORD PTR [edi+2044], eax
	mov eax, DWORD PTR [edi+1920]
	mov DWORD PTR [edi+2048], eax
	mov eax, DWORD PTR [edi+1924]
	mov DWORD PTR [edi+2052], eax
	mov eax, DWORD PTR [edi+1928]
	mov DWORD PTR [edi+2056], eax
	mov eax, DWORD PTR [edi+1932]
	mov DWORD PTR [edi+2060], eax
	mov eax, DWORD PTR [edi+1936]
	mov DWORD PTR [edi+2064], eax
	mov eax, DWORD PTR [edi+1940]
	mov DWORD PTR [edi+2068], eax
	mov eax, DWORD PTR [edi+1944]
	mov DWORD PTR [edi+2072], eax
	mov eax, DWORD PTR [edi+1948]
	mov DWORD PTR [edi+2076], eax
	mov eax, DWORD PTR [edi+1952]
	mov DWORD PTR [edi+2080], eax
	mov eax, DWORD PTR [edi+1956]
	mov DWORD PTR [edi+2084], eax
	mov eax, DWORD PTR [edi+1960]
	mov DWORD PTR [edi+2088], eax
	mov eax, DWORD PTR [edi+1964]
	mov DWORD PTR [edi+2092], eax
	mov esi, 2
23:
	mov eax, 1984
	mov ecx, 1984
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 23b
	mov eax, 1984
	mov ecx, 1984
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1984]
	mov DWORD PTR [edi+2112], eax
	mov eax, DWORD PTR [edi+1988]
	mov DWORD PTR [edi+2116], eax
	mov eax, DWORD PTR [edi+1992]
	mov DWORD PTR [edi+2120], eax
	mov eax, DWORD PTR [edi+1996]
	mov DWORD PTR [edi+2124], eax
	mov eax, DWORD PTR [edi+2000]
	mov DWORD PTR [edi+2128], eax
	mov eax, DWORD PTR [edi+2004]
	mov DWORD PTR [edi+2132], eax
	mov eax, DWORD PTR [edi+2008]
	mov DWORD PTR [edi+2136], eax
	mov eax, DWORD PTR [edi+2012]
	mov DWORD PTR [edi+2140], eax
	mov eax, DWORD PTR [edi+2016]
	mov DWORD PTR [edi+2144], eax
	mov eax, DWORD PTR [edi+2020]
	mov DWORD PTR [edi+2148], eax
	mov eax, DWORD PTR [edi+2024]
	mov DWORD PTR [edi+2152], eax
	mov eax, DWORD PTR [edi+2028]
	mov DWORD PTR [edi+2156], eax
	mov eax, DWORD PTR [edi+2032]
	mov DWORD PTR [edi+2160], eax
	mov eax, DWORD PTR [edi+2036]
	mov DWORD PTR [edi+2164], eax
	mov eax, DWORD PTR [edi+2040]
	mov DWORD PTR [edi+2168], eax
	mov eax, DWORD PTR [edi+2044]
	mov DWORD PTR [edi+2172], eax
	mov eax, DWORD PTR [edi+2048]
	mov DWORD PTR [edi+2176], eax
	mov eax, DWORD PTR [edi+2052]
	mov DWORD PTR [edi+2180], eax
	mov eax, DWORD PTR [edi+2056]
	mov DWORD PTR [edi+2184], eax
	mov eax, DWORD PTR [edi+2060]
	mov DWORD PTR [edi+2188], eax
	mov eax, DWORD PTR [edi+2064]
	mov DWORD PTR [edi+2192], eax
	mov eax, DWORD PTR [edi+2068]
	mov DWORD PTR [edi+2196], eax
	mov eax, DWORD PTR [edi+2072]
	mov DWORD PTR [edi+2200], eax
	mov eax, DWORD PTR [edi+2076]
	mov DWORD PTR [edi+2204], eax
	mov eax, DWORD PTR [edi+2080]
	mov DWORD PTR [edi+2208], eax
	mov eax, DWORD PTR [edi+2084]
	mov DWORD PTR [edi+2212], eax
	mov eax, DWORD PTR [edi+2088]
	mov DWORD PTR [edi+2216], eax
	mov eax, DWORD PTR [edi+2092]
	mov DWORD PTR [edi+2220], eax
	mov esi, 4
24:
	mov eax, 2112
	mov ecx, 2112
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 24b
	mov eax, 2112
	mov ecx, 2112
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2112]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2116]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2120]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2124]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2128]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2132]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2136]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2140]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2144]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2148]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2300], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2304], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2308], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2312], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2316], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2320], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2324], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2328], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2332], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2336], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2340], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2344], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2348], eax
	mov esi, 8
25:
	mov eax, 2240
	mov ecx, 2240
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 25b
	mov eax, 2240
	mov ecx, 2240
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2240]
	mov DWORD PTR [edi+2368], eax
	mov eax, DWORD PTR [edi+2244]
	mov DWORD PTR [edi+2372], eax
	mov eax, DWORD PTR [edi+2248]
	mov DWORD PTR [edi+2376], eax
	mov eax, DWORD PTR [edi+2252]
	mov DWORD PTR [edi+2380], eax
	mov eax, DWORD PTR [edi+2256]
	mov DWORD PTR [edi+2384], eax
	mov eax, DWORD PTR [edi+2260]
	mov DWORD PTR [edi+2388], eax
	mov eax, DWORD PTR [edi+2264]
	mov DWORD PTR [edi+2392], eax
	mov eax, DWORD PTR [edi+2268]
	mov DWORD PTR [edi+2396], eax
	mov eax, DWORD PTR [edi+2272]
	mov DWORD PTR [edi+2400], eax
	mov eax, DWORD PTR [edi+2276]
	mov DWORD PTR [edi+2404], eax
	mov eax, DWORD PTR [edi+2280]
	mov DWORD PTR [edi+2408], eax
	mov eax, DWORD PTR [edi+2284]
	mov DWORD PTR [edi+2412], eax
	mov eax, DWORD PTR [edi+2288]
	mov DWORD PTR [edi+2416], eax
	mov eax, DWORD PTR [edi+2292]
	mov DWORD PTR [edi+2420], eax
	mov eax, DWORD PTR [edi+2296]
	mov DWORD PTR [edi+2424], eax
	mov eax, DWORD PTR [edi+2300]
	mov DWORD PTR [edi+2428], eax
	mov eax, DWORD PTR [edi+2304]
	mov DWORD PTR [edi+2432], eax
	mov eax, DWORD PTR [edi+2308]
	mov DWORD PTR [edi+2436], eax
	mov eax, DWORD PTR [edi+2312]
	mov DWORD PTR [edi+2440], eax
	mov eax, DWORD PTR [edi+2316]
	mov DWORD PTR [edi+2444], eax
	mov eax, DWORD PTR [edi+2320]
	mov DWORD PTR [edi+2448], eax
	mov eax, DWORD PTR [edi+2324]
	mov DWORD PTR [edi+2452], eax
	mov eax, DWORD PTR [edi+2328]
	mov DWORD PTR [edi+2456], eax
	mov eax, DWORD PTR [edi+2332]
	mov DWORD PTR [edi+2460], eax
	mov eax, DWORD PTR [edi+2336]
	mov DWORD PTR [edi+2464], eax
	mov eax, DWORD PTR [edi+2340]
	mov DWORD PTR [edi+2468], eax
	mov eax, DWORD PTR [edi+2344]
	mov DWORD PTR [edi+2472], eax
	mov eax, DWORD PTR [edi+2348]
	mov DWORD PTR [edi+2476], eax
	mov esi, 16
26:
	mov eax, 2368
	mov ecx, 2368
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 26b
	mov eax, 2368
	mov ecx, 2368
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2368]
	mov DWORD PTR [edi+2496], eax
	mov eax, DWORD PTR [edi+2372]
	mov DWORD PTR [edi+2500], eax
	mov eax, DWORD PTR [edi+2376]
	mov DWORD PTR [edi+2504], eax
	mov eax, DWORD PTR [edi+2380]
	mov DWORD PTR [edi+2508], eax
	mov eax, DWORD PTR [edi+2384]
	mov DWORD PTR [edi+2512], eax
	mov eax, DWORD PTR [edi+2388]
	mov DWORD PTR [edi+2516], eax
	mov eax, DWORD PTR [edi+2392]
	mov DWORD PTR [edi+2520], eax
	mov eax, DWORD PTR [edi+2396]
	mov DWORD PTR [edi+2524], eax
	mov eax, DWORD PTR [edi+2400]
	mov DWORD PTR [edi+2528], eax
	mov eax, DWORD PTR [edi+2404]
	mov DWORD PTR [edi+2532], eax
	mov eax, DWORD PTR [edi+2408]
	mov DWORD PTR [edi+2536], eax
	mov eax, DWORD PTR [edi+2412]
	mov DWORD PTR [edi+2540], eax
	mov eax, DWORD PTR [edi+2416]
	mov DWORD PTR [edi+2544], eax
	mov eax, DWORD PTR [edi+2420]
	mov DWORD PTR [edi+2548], eax
	mov eax, DWORD PTR [edi+2424]
	mov DWORD PTR [edi+2552], eax
	mov eax, DWORD PTR [edi+2428]
	mov DWORD PTR [edi+2556], eax
	mov eax, DWORD PTR [edi+2432]
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2436]
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2440]
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2444]
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2448]
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2452]
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2456]
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2460]
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2464]
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2468]
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2472]
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2476]
	mov DWORD PTR [edi+2604], eax
	mov esi, 32
27:
	mov eax, 2496
	mov ecx, 2496
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 27b
	mov eax, 2496
	mov ecx, 2496
	mov edx, 2368
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2496]
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2500]
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2504]
	mov DWORD PTR [edi+2632], eax
	mov eax, DWORD PTR [edi+2508]
	mov DWORD PTR [edi+2636], eax
	mov eax, DWORD PTR [edi+2512]
	mov DWORD PTR [edi+2640], eax
	mov eax, DWORD PTR [edi+2516]
	mov DWORD PTR [edi+2644], eax
	mov eax, DWORD PTR [edi+2520]
	mov DWORD PTR [edi+2648], eax
	mov eax, DWORD PTR [edi+2524]
	mov DWORD PTR [edi+2652], eax
	mov eax, DWORD PTR [edi+2528]
	mov DWORD PTR [edi+2656], eax
	mov eax, DWORD PTR [edi+2532]
	mov DWORD PTR [edi+2660], eax
	mov eax, DWORD PTR [edi+2536]
	mov DWORD PTR [edi+2664], eax
	mov eax, DWORD PTR [edi+2540]
	mov DWORD PTR [edi+2668], eax
	mov eax, DWORD PTR [edi+2544]
	mov DWORD PTR [edi+2672], eax
	mov eax, DWORD PTR [edi+2548]
	mov DWORD PTR [edi+2676], eax
	mov eax, DWORD PTR [edi+2552]
	mov DWORD PTR [edi+2680], eax
	mov eax, DWORD PTR [edi+2556]
	mov DWORD PTR [edi+2684], eax
	mov eax, DWORD PTR [edi+2560]
	mov DWORD PTR [edi+2688], eax
	mov eax, DWORD PTR [edi+2564]
	mov DWORD PTR [edi+2692], eax
	mov eax, DWORD PTR [edi+2568]
	mov DWORD PTR [edi+2696], eax
	mov eax, DWORD PTR [edi+2572]
	mov DWORD PTR [edi+2700], eax
	mov eax, DWORD PTR [edi+2576]
	mov DWORD PTR [edi+2704], eax
	mov eax, DWORD PTR [edi+2580]
	mov DWORD PTR [edi+2708], eax
	mov eax, DWORD PTR [edi+2584]
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+2588]
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2592]
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2596]
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+2600]
	mov DWORD PTR [edi+2728], eax
	mov eax, DWORD PTR [edi+2604]
	mov DWORD PTR [edi+2732], eax
	mov esi, 64
28:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 28b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 64
29:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 29b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2496
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 16
210:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 210b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 8
211:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 211b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 4
212:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 212b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 2
213:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 213b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2624]
	mov DWORD PTR [edi+2752], eax
	mov eax, DWORD PTR [edi+2628]
	mov DWORD PTR [edi+2756], eax
	mov eax, DWORD PTR [edi+2632]
	mov DWORD PTR [edi+2760], eax
	mov eax, DWORD PTR [edi+2636]
	mov DWORD PTR [edi+2764], eax
	mov eax, DWORD PTR [edi+2640]
	mov DWORD PTR [edi+2768], eax
	mov eax, DWORD PTR [edi+2644]
	mov DWORD PTR [edi+2772], eax
	mov eax, DWORD PTR [edi+2648]
	mov DWORD PTR [edi+2776], eax
	mov eax, DWORD PTR [edi+2652]
	mov DWORD PTR [edi+2780], eax
	mov eax, DWORD PTR [edi+2656]
	mov DWORD PTR [edi+2784], eax
	mov eax, DWORD PTR [edi+2660]
	mov DWORD PTR [edi+2788], eax
	mov eax, DWORD PTR [edi+2664]
	mov DWORD PTR [edi+2792], eax
	mov eax, DWORD PTR [edi+2668]
	mov DWORD PTR [edi+2796], eax
	mov eax, DWORD PTR [edi+2672]
	mov DWORD PTR [edi+2800], eax
	mov eax, DWORD PTR [edi+2676]
	mov DWORD PTR [edi+2804], eax
	mov eax, DWORD PTR [edi+2680]
	mov DWORD PTR [edi+2808], eax
	mov eax, DWORD PTR [edi+2684]
	mov DWORD PTR [edi+2812], eax
	mov eax, DWORD PTR [edi+2688]
	mov DWORD PTR [edi+2816], eax
	mov eax, DWORD PTR [edi+2692]
	mov DWORD PTR [edi+2820], eax
	mov eax, DWORD PTR [edi+2696]
	mov DWORD PTR [edi+2824], eax
	mov eax, DWORD PTR [edi+2700]
	mov DWORD PTR [edi+2828], eax
	mov eax, DWORD PTR [edi+2704]
	mov DWORD PTR [edi+2832], eax
	mov eax, DWORD PTR [edi+2708]
	mov DWORD PTR [edi+2836], eax
	mov eax, DWORD PTR [edi+2712]
	mov DWORD PTR [edi+2840], eax
	mov eax, DWORD PTR [edi+2716]
	mov DWORD PTR [edi+2844], eax
	mov eax, DWORD PTR [edi+2720]
	mov DWORD PTR [edi+2848], eax
	mov eax, DWORD PTR [edi+2724]
	mov DWORD PTR [edi+2852], eax
	mov eax, DWORD PTR [edi+2728]
	mov DWORD PTR [edi+2856], eax
	mov eax, DWORD PTR [edi+2732]
	mov DWORD PTR [edi+2860], eax
	mov esi, 1
214:
	mov eax, 2752
	mov ecx, 2752
	mov edx, 2752
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 214b
	mov eax, 2752
	mov ecx, 2752
	mov edx, 320
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 225
215:
	mov eax, 2752
	mov ecx, 2752
	mov edx, 2752
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 215b
	mov esi, 2
216:
	mov eax, 2624
	mov ecx, 2624
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 216b
	mov eax, 2624
	mov ecx, 2624
	mov edx, 320
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2752
	mov ecx, 2752
	mov edx, 2624
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 192
	mov ecx, 192
	mov edx, 2752
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3892], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3896], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3900], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3904], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3908], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3912], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3916], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3920], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3924], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3928], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3932], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3936], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3940], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3944], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3948], eax
	mov eax, DWORD PTR [edi+3840]
	add eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+3896]
	add eax, 1
	mov DWORD PTR [edi+3896], eax
	mov ebx, 0
	mov eax, DWORD PTR [edi+3840]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3840], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3844]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3844], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3848]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3848], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3852]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3852], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3856]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3856], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3860]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3860], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3864]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3864], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3868]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3868], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3872]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3872], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3876]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3876], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3880]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3880], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3884]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3884], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3888]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3888], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3892]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3892], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3896]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3896], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3900]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3900], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3904]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3904], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3908]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3908], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3912]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3912], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3916]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3916], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3920]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3920], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3924]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3924], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3928]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3928], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3932]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3932], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3936]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3936], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3940]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3940], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3944]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3944], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3948]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3948], edx
	shr ebx, 16
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+3840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+3844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+3848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+3852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+3856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+3860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+3864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+3868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+3872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+3876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+3880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+3884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+3888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+3892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+3896]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+3900]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+3904]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+3908]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+3912]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+3916]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+3920]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+3924]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+3928]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+3932]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+3936]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+3940]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+3944]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+3948]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+300], eax
	mov esi, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+192]
	mov BYTE PTR [esi], al
	shr eax, 8
	mov BYTE PTR [esi+1], al
	mov eax, DWORD PTR [edi+196]
	mov BYTE PTR [esi+2], al
	shr eax, 8
	mov BYTE PTR [esi+3], al
	mov eax, DWORD PTR [edi+200]
	mov BYTE PTR [esi+4], al
	shr eax, 8
	mov BYTE PTR [esi+5], al
	mov eax, DWORD PTR [edi+204]
	mov BYTE PTR [esi+6], al
	shr eax, 8
	mov BYTE PTR [esi+7], al
	mov eax, DWORD PTR [edi+208]
	mov BYTE PTR [esi+8], al
	shr eax, 8
	mov BYTE PTR [esi+9], al
	mov eax, DWORD PTR [edi+212]
	mov BYTE PTR [esi+10], al
	shr eax, 8
	mov BYTE PTR [esi+11], al
	mov eax, DWORD PTR [edi+216]
	mov BYTE PTR [esi+12], al
	shr eax, 8
	mov BYTE PTR [esi+13], al
	mov eax, DWORD PTR [edi+220]
	mov BYTE PTR [esi+14], al
	shr eax, 8
	mov BYTE PTR [esi+15], al
	mov eax, DWORD PTR [edi+224]
	mov BYTE PTR [esi+16], al
	shr eax, 8
	mov BYTE PTR [esi+17], al
	mov eax, DWORD PTR [edi+228]
	mov BYTE PTR [esi+18], al
	shr eax, 8
	mov BYTE PTR [esi+19], al
	mov eax, DWORD PTR [edi+232]
	mov BYTE PTR [esi+20], al
	shr eax, 8
	mov BYTE PTR [esi+21], al
	mov eax, DWORD PTR [edi+236]
	mov BYTE PTR [esi+22], al
	shr eax, 8
	mov BYTE PTR [esi+23], al
	mov eax, DWORD PTR [edi+240]
	mov BYTE PTR [esi+24], al
	shr eax, 8
	mov BYTE PTR [esi+25], al
	mov eax, DWORD PTR [edi+244]
	mov BYTE PTR [esi+26], al
	shr eax, 8
	mov BYTE PTR [esi+27], al
	mov eax, DWORD PTR [edi+248]
	mov BYTE PTR [esi+28], al
	shr eax, 8
	mov BYTE PTR [esi+29], al
	mov eax, DWORD PTR [edi+252]
	mov BYTE PTR [esi+30], al
	shr eax, 8
	mov BYTE PTR [esi+31], al
	mov eax, DWORD PTR [edi+256]
	mov BYTE PTR [esi+32], al
	shr eax, 8
	mov BYTE PTR [esi+33], al
	mov eax, DWORD PTR [edi+260]
	mov BYTE PTR [esi+34], al
	shr eax, 8
	mov BYTE PTR [esi+35], al
	mov eax, DWORD PTR [edi+264]
	mov BYTE PTR [esi+36], al
	shr eax, 8
	mov BYTE PTR [esi+37], al
	mov eax, DWORD PTR [edi+268]
	mov BYTE PTR [esi+38], al
	shr eax, 8
	mov BYTE PTR [esi+39], al
	mov eax, DWORD PTR [edi+272]
	mov BYTE PTR [esi+40], al
	shr eax, 8
	mov BYTE PTR [esi+41], al
	mov eax, DWORD PTR [edi+276]
	mov BYTE PTR [esi+42], al
	shr eax, 8
	mov BYTE PTR [esi+43], al
	mov eax, DWORD PTR [edi+280]
	mov BYTE PTR [esi+44], al
	shr eax, 8
	mov BYTE PTR [esi+45], al
	mov eax, DWORD PTR [edi+284]
	mov BYTE PTR [esi+46], al
	shr eax, 8
	mov BYTE PTR [esi+47], al
	mov eax, DWORD PTR [edi+288]
	mov BYTE PTR [esi+48], al
	shr eax, 8
	mov BYTE PTR [esi+49], al
	mov eax, DWORD PTR [edi+292]
	mov BYTE PTR [esi+50], al
	shr eax, 8
	mov BYTE PTR [esi+51], al
	mov eax, DWORD PTR [edi+296]
	mov BYTE PTR [esi+52], al
	shr eax, 8
	mov BYTE PTR [esi+53], al
	mov eax, DWORD PTR [edi+300]
	mov BYTE PTR [esi+54], al
	shr eax, 8
	mov BYTE PTR [esi+55], al
	mov eax, edi
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov ebp, DWORD PTR [eax+12]
	mov edi, DWORD PTR [eax+8]
	ret
	.p2align 6
