// The functions of `src/sm4_gcm.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ctr32:
	lea esp, [esp-1496]
	mov eax, DWORD PTR [esp+1500]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1504]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1508]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1512]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+1432], ebx
	mov DWORD PTR [eax+1436], esi
	mov DWORD PTR [eax+1440], edi
	mov DWORD PTR [eax+1444], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1468], eax
	mov eax, 179
	mov edx, 0
	mov ecx, DWORD PTR [esp+4]
	push eax
	push edi
	push edx
	push ecx
	call {vg_sm4_prepare_keys}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+1448], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+1452], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+1448]
	mov ebp, DWORD PTR [edi+1452]
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+268], eax
	mov esi, DWORD PTR [edi+1448]
	mov ebp, DWORD PTR [edi+1452]
	mov eax, 179
	push eax
	push edi
	call {vg_sm4_crypt_prepared}
	pop eax
	pop eax
	mov DWORD PTR [edi+1448], esi
	mov DWORD PTR [edi+1452], ebp
	mov esi, DWORD PTR [edi+1448]
	mov ebp, DWORD PTR [edi+1452]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+256]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+260]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+264]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+268]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+1468]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1468], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+1448], esi
	mov DWORD PTR [edi+1452], ebp
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+1432]
	mov esi, DWORD PTR [edi+1436]
	mov ebp, DWORD PTR [edi+1444]
	mov edi, DWORD PTR [edi+1440]
	mov ecx, 0
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
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
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
	mov DWORD PTR [esp+512], ecx
	mov DWORD PTR [esp+516], ecx
	mov DWORD PTR [esp+520], ecx
	mov DWORD PTR [esp+524], ecx
	mov DWORD PTR [esp+528], ecx
	mov DWORD PTR [esp+532], ecx
	mov DWORD PTR [esp+536], ecx
	mov DWORD PTR [esp+540], ecx
	mov DWORD PTR [esp+544], ecx
	mov DWORD PTR [esp+548], ecx
	mov DWORD PTR [esp+552], ecx
	mov DWORD PTR [esp+556], ecx
	mov DWORD PTR [esp+560], ecx
	mov DWORD PTR [esp+564], ecx
	mov DWORD PTR [esp+568], ecx
	mov DWORD PTR [esp+572], ecx
	mov DWORD PTR [esp+576], ecx
	mov DWORD PTR [esp+580], ecx
	mov DWORD PTR [esp+584], ecx
	mov DWORD PTR [esp+588], ecx
	mov DWORD PTR [esp+592], ecx
	mov DWORD PTR [esp+596], ecx
	mov DWORD PTR [esp+600], ecx
	mov DWORD PTR [esp+604], ecx
	mov DWORD PTR [esp+608], ecx
	mov DWORD PTR [esp+612], ecx
	mov DWORD PTR [esp+616], ecx
	mov DWORD PTR [esp+620], ecx
	mov DWORD PTR [esp+624], ecx
	mov DWORD PTR [esp+628], ecx
	mov DWORD PTR [esp+632], ecx
	mov DWORD PTR [esp+636], ecx
	mov DWORD PTR [esp+640], ecx
	mov DWORD PTR [esp+644], ecx
	mov DWORD PTR [esp+648], ecx
	mov DWORD PTR [esp+652], ecx
	mov DWORD PTR [esp+656], ecx
	mov DWORD PTR [esp+660], ecx
	mov DWORD PTR [esp+664], ecx
	mov DWORD PTR [esp+668], ecx
	mov DWORD PTR [esp+672], ecx
	mov DWORD PTR [esp+676], ecx
	mov DWORD PTR [esp+680], ecx
	mov DWORD PTR [esp+684], ecx
	mov DWORD PTR [esp+688], ecx
	mov DWORD PTR [esp+692], ecx
	mov DWORD PTR [esp+696], ecx
	mov DWORD PTR [esp+700], ecx
	mov DWORD PTR [esp+704], ecx
	mov DWORD PTR [esp+708], ecx
	mov DWORD PTR [esp+712], ecx
	mov DWORD PTR [esp+716], ecx
	mov DWORD PTR [esp+720], ecx
	mov DWORD PTR [esp+724], ecx
	mov DWORD PTR [esp+728], ecx
	mov DWORD PTR [esp+732], ecx
	mov DWORD PTR [esp+736], ecx
	mov DWORD PTR [esp+740], ecx
	mov DWORD PTR [esp+744], ecx
	mov DWORD PTR [esp+748], ecx
	mov DWORD PTR [esp+752], ecx
	mov DWORD PTR [esp+756], ecx
	mov DWORD PTR [esp+760], ecx
	mov DWORD PTR [esp+764], ecx
	mov DWORD PTR [esp+768], ecx
	mov DWORD PTR [esp+772], ecx
	mov DWORD PTR [esp+776], ecx
	mov DWORD PTR [esp+780], ecx
	mov DWORD PTR [esp+784], ecx
	mov DWORD PTR [esp+788], ecx
	mov DWORD PTR [esp+792], ecx
	mov DWORD PTR [esp+796], ecx
	mov DWORD PTR [esp+800], ecx
	mov DWORD PTR [esp+804], ecx
	mov DWORD PTR [esp+808], ecx
	mov DWORD PTR [esp+812], ecx
	mov DWORD PTR [esp+816], ecx
	mov DWORD PTR [esp+820], ecx
	mov DWORD PTR [esp+824], ecx
	mov DWORD PTR [esp+828], ecx
	mov DWORD PTR [esp+832], ecx
	mov DWORD PTR [esp+836], ecx
	mov DWORD PTR [esp+840], ecx
	mov DWORD PTR [esp+844], ecx
	mov DWORD PTR [esp+848], ecx
	mov DWORD PTR [esp+852], ecx
	mov DWORD PTR [esp+856], ecx
	mov DWORD PTR [esp+860], ecx
	mov DWORD PTR [esp+864], ecx
	mov DWORD PTR [esp+868], ecx
	mov DWORD PTR [esp+872], ecx
	mov DWORD PTR [esp+876], ecx
	mov DWORD PTR [esp+880], ecx
	mov DWORD PTR [esp+884], ecx
	mov DWORD PTR [esp+888], ecx
	mov DWORD PTR [esp+892], ecx
	mov DWORD PTR [esp+896], ecx
	mov DWORD PTR [esp+900], ecx
	mov DWORD PTR [esp+904], ecx
	mov DWORD PTR [esp+908], ecx
	mov DWORD PTR [esp+912], ecx
	mov DWORD PTR [esp+916], ecx
	mov DWORD PTR [esp+920], ecx
	mov DWORD PTR [esp+924], ecx
	mov DWORD PTR [esp+928], ecx
	mov DWORD PTR [esp+932], ecx
	mov DWORD PTR [esp+936], ecx
	mov DWORD PTR [esp+940], ecx
	mov DWORD PTR [esp+944], ecx
	mov DWORD PTR [esp+948], ecx
	mov DWORD PTR [esp+952], ecx
	mov DWORD PTR [esp+956], ecx
	mov DWORD PTR [esp+960], ecx
	mov DWORD PTR [esp+964], ecx
	mov DWORD PTR [esp+968], ecx
	mov DWORD PTR [esp+972], ecx
	mov DWORD PTR [esp+976], ecx
	mov DWORD PTR [esp+980], ecx
	mov DWORD PTR [esp+984], ecx
	mov DWORD PTR [esp+988], ecx
	mov DWORD PTR [esp+992], ecx
	mov DWORD PTR [esp+996], ecx
	mov DWORD PTR [esp+1000], ecx
	mov DWORD PTR [esp+1004], ecx
	mov DWORD PTR [esp+1008], ecx
	mov DWORD PTR [esp+1012], ecx
	mov DWORD PTR [esp+1016], ecx
	mov DWORD PTR [esp+1020], ecx
	mov DWORD PTR [esp+1024], ecx
	mov DWORD PTR [esp+1028], ecx
	mov DWORD PTR [esp+1032], ecx
	mov DWORD PTR [esp+1036], ecx
	mov DWORD PTR [esp+1040], ecx
	mov DWORD PTR [esp+1044], ecx
	mov DWORD PTR [esp+1048], ecx
	mov DWORD PTR [esp+1052], ecx
	mov DWORD PTR [esp+1056], ecx
	mov DWORD PTR [esp+1060], ecx
	mov DWORD PTR [esp+1064], ecx
	mov DWORD PTR [esp+1068], ecx
	mov DWORD PTR [esp+1072], ecx
	mov DWORD PTR [esp+1076], ecx
	mov DWORD PTR [esp+1080], ecx
	mov DWORD PTR [esp+1084], ecx
	mov DWORD PTR [esp+1088], ecx
	mov DWORD PTR [esp+1092], ecx
	mov DWORD PTR [esp+1096], ecx
	mov DWORD PTR [esp+1100], ecx
	mov DWORD PTR [esp+1104], ecx
	mov DWORD PTR [esp+1108], ecx
	mov DWORD PTR [esp+1112], ecx
	mov DWORD PTR [esp+1116], ecx
	mov DWORD PTR [esp+1120], ecx
	mov DWORD PTR [esp+1124], ecx
	mov DWORD PTR [esp+1128], ecx
	mov DWORD PTR [esp+1132], ecx
	mov DWORD PTR [esp+1136], ecx
	mov DWORD PTR [esp+1140], ecx
	mov DWORD PTR [esp+1144], ecx
	mov DWORD PTR [esp+1148], ecx
	mov DWORD PTR [esp+1152], ecx
	mov DWORD PTR [esp+1156], ecx
	mov DWORD PTR [esp+1160], ecx
	mov DWORD PTR [esp+1164], ecx
	mov DWORD PTR [esp+1168], ecx
	mov DWORD PTR [esp+1172], ecx
	mov DWORD PTR [esp+1176], ecx
	mov DWORD PTR [esp+1180], ecx
	mov DWORD PTR [esp+1184], ecx
	mov DWORD PTR [esp+1188], ecx
	mov DWORD PTR [esp+1192], ecx
	mov DWORD PTR [esp+1196], ecx
	mov DWORD PTR [esp+1200], ecx
	mov DWORD PTR [esp+1204], ecx
	mov DWORD PTR [esp+1208], ecx
	mov DWORD PTR [esp+1212], ecx
	mov DWORD PTR [esp+1216], ecx
	mov DWORD PTR [esp+1220], ecx
	mov DWORD PTR [esp+1224], ecx
	mov DWORD PTR [esp+1228], ecx
	mov DWORD PTR [esp+1232], ecx
	mov DWORD PTR [esp+1236], ecx
	mov DWORD PTR [esp+1240], ecx
	mov DWORD PTR [esp+1244], ecx
	mov DWORD PTR [esp+1248], ecx
	mov DWORD PTR [esp+1252], ecx
	mov DWORD PTR [esp+1256], ecx
	mov DWORD PTR [esp+1260], ecx
	mov DWORD PTR [esp+1264], ecx
	mov DWORD PTR [esp+1268], ecx
	mov DWORD PTR [esp+1272], ecx
	mov DWORD PTR [esp+1276], ecx
	mov DWORD PTR [esp+1280], ecx
	mov DWORD PTR [esp+1284], ecx
	mov DWORD PTR [esp+1288], ecx
	mov DWORD PTR [esp+1292], ecx
	mov DWORD PTR [esp+1296], ecx
	mov DWORD PTR [esp+1300], ecx
	mov DWORD PTR [esp+1304], ecx
	mov DWORD PTR [esp+1308], ecx
	mov DWORD PTR [esp+1312], ecx
	mov DWORD PTR [esp+1316], ecx
	mov DWORD PTR [esp+1320], ecx
	mov DWORD PTR [esp+1324], ecx
	mov DWORD PTR [esp+1328], ecx
	mov DWORD PTR [esp+1332], ecx
	mov DWORD PTR [esp+1336], ecx
	mov DWORD PTR [esp+1340], ecx
	mov DWORD PTR [esp+1344], ecx
	mov DWORD PTR [esp+1348], ecx
	mov DWORD PTR [esp+1352], ecx
	mov DWORD PTR [esp+1356], ecx
	mov DWORD PTR [esp+1360], ecx
	mov DWORD PTR [esp+1364], ecx
	mov DWORD PTR [esp+1368], ecx
	mov DWORD PTR [esp+1372], ecx
	mov DWORD PTR [esp+1376], ecx
	mov DWORD PTR [esp+1380], ecx
	mov DWORD PTR [esp+1384], ecx
	mov DWORD PTR [esp+1388], ecx
	mov DWORD PTR [esp+1392], ecx
	mov DWORD PTR [esp+1396], ecx
	mov DWORD PTR [esp+1400], ecx
	mov DWORD PTR [esp+1404], ecx
	mov DWORD PTR [esp+1408], ecx
	mov DWORD PTR [esp+1412], ecx
	mov DWORD PTR [esp+1416], ecx
	mov DWORD PTR [esp+1420], ecx
	mov DWORD PTR [esp+1424], ecx
	mov DWORD PTR [esp+1428], ecx
	mov DWORD PTR [esp+1432], ecx
	mov DWORD PTR [esp+1436], ecx
	mov DWORD PTR [esp+1440], ecx
	mov DWORD PTR [esp+1444], ecx
	mov DWORD PTR [esp+1448], ecx
	mov DWORD PTR [esp+1452], ecx
	mov DWORD PTR [esp+1456], ecx
	mov DWORD PTR [esp+1460], ecx
	mov DWORD PTR [esp+1464], ecx
	mov DWORD PTR [esp+1468], ecx
	mov DWORD PTR [esp+1472], ecx
	mov DWORD PTR [esp+1476], ecx
	mov DWORD PTR [esp+1480], ecx
	mov DWORD PTR [esp+1484], ecx
	mov DWORD PTR [esp+1488], ecx
	mov DWORD PTR [esp+1492], ecx
	lea esp, [esp+1496]
	ret
	.p2align 6

vg_sm4_gcm_init:
	lea esp, [esp-2576]
	mov eax, DWORD PTR [esp+2580]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2584]
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 16
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	mov edx, esi
	push edx
	push eax
	call {vg_sm4_expand_key}
	pop eax
	pop eax
	mov eax, 0
	mov DWORD PTR [esi+240], eax
	mov DWORD PTR [esi+244], eax
	mov DWORD PTR [esi+248], eax
	mov DWORD PTR [esi+252], eax
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov eax, esi
	mov edx, ebp
	add edx, 96
	mov ebx, esi
	add ebx, 240
	mov edi, 1
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2576]
	ret
	.p2align 6

vg_sm4_gcm_stream_init_pclmul:
	lea esp, [esp-2584]
	mov eax, DWORD PTR [esp+2588]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2592]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2596]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2600]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+192], eax
	mov eax, 0
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [ebp+192]
	cmp eax, 12
	je 20f
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 22f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 24f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 26f
	jmp 27f
26:
	mov ecx, eax
27:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
28:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 28b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 29f
	jmp 210f
29:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
210:
	jmp 25f
24:
25:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 211f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 212f
211:
212:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 213f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
215:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 215b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov eax, DWORD PTR [ebp+192]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 216f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
218:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 218b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 217f
216:
217:
	mov eax, DWORD PTR [ebp+188]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 21f
20:
	mov edi, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], ecx
	mov DWORD PTR [esi+8], edx
	mov eax, 16777216
	mov DWORD PTR [esi+12], eax
21:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [esi+60], eax
	mov eax, 0
	mov DWORD PTR [esi+16], eax
	mov DWORD PTR [esi+20], eax
	mov DWORD PTR [esi+24], eax
	mov DWORD PTR [esi+28], eax
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2584]
	ret
	.p2align 6

vg_sm4_gcm_stream_aad_pclmul:
	lea esp, [esp-2592]
	mov eax, DWORD PTR [esp+2596]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2600]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2604]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2608]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [esp+12]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 20f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 22f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 24f
	jmp 25f
24:
	mov ecx, eax
25:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
26:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 26b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 27f
	jmp 28f
27:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
28:
	jmp 23f
22:
23:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 29f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 210f
29:
210:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 211f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
213:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	jmp 212f
211:
212:
	jmp 21f
20:
21:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2592]
	ret
	.p2align 6

vg_sm4_gcm_stream_encrypt_pclmul:
	lea esp, [esp-2600]
	mov eax, DWORD PTR [esp+2604]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2608]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+32], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+172], eax
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+160]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 20f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 22f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 24f
	jmp 25f
24:
	mov ecx, eax
25:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
26:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 26b
	jmp 23f
22:
23:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 27f
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	add edx, 48
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 28f
27:
28:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 29f
	mov eax, 0
	mov DWORD PTR [esi+64], eax
	mov DWORD PTR [esi+68], eax
	mov DWORD PTR [esi+72], eax
	mov DWORD PTR [esi+76], eax
	mov ebx, esi
	add ebx, 64
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	add edx, 48
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	mov ecx, DWORD PTR [ebp+276]
211:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 211b
	jmp 210f
29:
210:
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebp+172]
	test eax, eax
	je 212f
	mov eax, DWORD PTR [ebp+160]
	or eax, DWORD PTR [ebp+164]
	je 214f
	jmp 215f
214:
	mov eax, DWORD PTR [ebp+152]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 216f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
218:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 218b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 217f
216:
217:
215:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+160]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 219f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 221f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 223f
	jmp 224f
223:
	mov ecx, eax
224:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
225:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 225b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 226f
	jmp 227f
226:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
227:
	jmp 222f
221:
222:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 228f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 229f
228:
229:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 230f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
232:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 232b
	jmp 231f
230:
231:
	jmp 220f
219:
220:
	jmp 213f
212:
213:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2600]
	ret
	.p2align 6

vg_sm4_gcm_stream_decrypt_pclmul:
	lea esp, [esp-2600]
	mov eax, DWORD PTR [esp+2604]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2608]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+32], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+172], eax
	mov eax, DWORD PTR [ebp+172]
	test eax, eax
	je 20f
	mov eax, DWORD PTR [ebp+160]
	or eax, DWORD PTR [ebp+164]
	je 22f
	jmp 23f
22:
	mov eax, DWORD PTR [ebp+152]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 24f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
26:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 26b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 25f
24:
25:
23:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+160]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 27f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 29f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 211f
	jmp 212f
211:
	mov ecx, eax
212:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
213:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 214f
	jmp 215f
214:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
215:
	jmp 210f
29:
210:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 216f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 217f
216:
217:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 218f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
220:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 220b
	jmp 219f
218:
219:
	jmp 28f
27:
28:
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+160]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 221f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 223f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 225f
	jmp 226f
225:
	mov ecx, eax
226:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
227:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 227b
	jmp 224f
223:
224:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 228f
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	add edx, 48
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 229f
228:
229:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 230f
	mov eax, 0
	mov DWORD PTR [esi+64], eax
	mov DWORD PTR [esi+68], eax
	mov DWORD PTR [esi+72], eax
	mov DWORD PTR [esi+76], eax
	mov ebx, esi
	add ebx, 64
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	add edx, 48
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	mov ecx, DWORD PTR [ebp+276]
232:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 232b
	jmp 231f
230:
231:
	jmp 222f
221:
222:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2600]
	ret
	.p2align 6

vg_sm4_gcm_stream_finish_pclmul:
	lea esp, [esp-2596]
	mov eax, DWORD PTR [esp+2600]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2604]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2608]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+212], eax
	mov eax, DWORD PTR [ebp+160]
	mov ecx, DWORD PTR [ebp+152]
	mov edx, DWORD PTR [ebp+160]
	or edx, DWORD PTR [ebp+164]
	je 20f
	jmp 21f
20:
	mov eax, ecx
21:
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 22f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
24:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 24b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 23f
22:
23:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+156]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+160]
	mov ecx, DWORD PTR [ebp+164]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+20]
	mov edx, DWORD PTR [esi+24]
	mov ebx, DWORD PTR [esi+28]
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], ecx
	mov DWORD PTR [ebp+8], edx
	mov DWORD PTR [ebp+12], ebx
	mov ebx, ebp
	add ebx, 0
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp]
	mov ecx, DWORD PTR [ebp+4]
	mov edx, DWORD PTR [ebp+8]
	mov ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [ebp+212]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ecx
	mov DWORD PTR [edi+8], edx
	mov DWORD PTR [edi+12], ebx
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2596]
	ret
	.p2align 6

vg_sm4_gcm_stream_verify_pclmul:
	lea esp, [esp-2600]
	mov eax, DWORD PTR [esp+2604]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2608]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+32], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+212], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+180], eax
	mov ecx, 0
	mov ebx, DWORD PTR [ebp+180]
	cmp ebx, 4
	jb 20f
	cmp ebx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test ecx, ecx
	je 24f
	mov eax, 0
	mov DWORD PTR [ebp+196], eax
	mov DWORD PTR [ebp+200], eax
	mov DWORD PTR [ebp+204], eax
	mov DWORD PTR [ebp+208], eax
	mov edi, DWORD PTR [ebp+212]
	mov edx, ebp
	add edx, 196
	mov ecx, DWORD PTR [ebp+180]
26:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 26b
	mov eax, DWORD PTR [ebp+160]
	mov ecx, DWORD PTR [ebp+152]
	mov edx, DWORD PTR [ebp+160]
	or edx, DWORD PTR [ebp+164]
	je 27f
	jmp 28f
27:
	mov eax, ecx
28:
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 29f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
211:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 211b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 210f
29:
210:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+156]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+160]
	mov ecx, DWORD PTR [ebp+164]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+20]
	mov edx, DWORD PTR [esi+24]
	mov ebx, DWORD PTR [esi+28]
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], ecx
	mov DWORD PTR [ebp+8], edx
	mov DWORD PTR [ebp+12], ebx
	mov ebx, ebp
	add ebx, 0
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 0
	mov DWORD PTR [ebp+240], eax
	mov DWORD PTR [ebp+244], eax
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+252], eax
	mov edi, ebp
	add edi, 0
	mov edx, ebp
	add edx, 240
	mov ecx, DWORD PTR [ebp+180]
212:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 212b
	mov eax, DWORD PTR [ebp+240]
	xor eax, DWORD PTR [ebp+196]
	mov ecx, DWORD PTR [ebp+244]
	xor ecx, DWORD PTR [ebp+200]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+248]
	xor ecx, DWORD PTR [ebp+204]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+252]
	xor ecx, DWORD PTR [ebp+208]
	or eax, ecx
	cmp eax, 1
	mov eax, 0
	adc eax, 0
	jmp 25f
24:
	mov eax, 0
25:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2600]
	ret
	.p2align 6

vg_sm4_gcm_seal_pclmul:
	lea esp, [esp-2600]
	mov eax, DWORD PTR [esp+2604]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2608]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+32], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, ebp
	add esi, 16
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+172], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+212], eax
	mov eax, 0
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [ebp+192]
	cmp eax, 12
	je 20f
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 22f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 24f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 26f
	jmp 27f
26:
	mov ecx, eax
27:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
28:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 28b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 29f
	jmp 210f
29:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
210:
	jmp 25f
24:
25:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 211f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 212f
211:
212:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 213f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
215:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 215b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov eax, DWORD PTR [ebp+192]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 216f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
218:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 218b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 217f
216:
217:
	mov eax, DWORD PTR [ebp+188]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 21f
20:
	mov edi, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], ecx
	mov DWORD PTR [esi+8], edx
	mov eax, 16777216
	mov DWORD PTR [esi+12], eax
21:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [esi+60], eax
	mov eax, 0
	mov DWORD PTR [esi+16], eax
	mov DWORD PTR [esi+20], eax
	mov DWORD PTR [esi+24], eax
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [ebp+176]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+276], eax
	mov eax, 0
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 219f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 221f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 223f
	jmp 224f
223:
	mov ecx, eax
224:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
225:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 225b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 226f
	jmp 227f
226:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
227:
	jmp 222f
221:
222:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 228f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 229f
228:
229:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 230f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
232:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 232b
	jmp 231f
230:
231:
	jmp 220f
219:
220:
	mov eax, DWORD PTR [ebp+152]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 233f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
235:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 235b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 234f
233:
234:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, 0
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 236f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 238f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 240f
	jmp 241f
240:
	mov ecx, eax
241:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
242:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 242b
	jmp 239f
238:
239:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 243f
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	add edx, 48
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 244f
243:
244:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 245f
	mov eax, 0
	mov DWORD PTR [esi+64], eax
	mov DWORD PTR [esi+68], eax
	mov DWORD PTR [esi+72], eax
	mov DWORD PTR [esi+76], eax
	mov ebx, esi
	add ebx, 64
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	add edx, 48
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	mov ecx, DWORD PTR [ebp+276]
247:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 247b
	jmp 246f
245:
246:
	jmp 237f
236:
237:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, 0
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 248f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 250f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 252f
	jmp 253f
252:
	mov ecx, eax
253:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
254:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 254b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 255f
	jmp 256f
255:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
256:
	jmp 251f
250:
251:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 257f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 258f
257:
258:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 259f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
261:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 261b
	jmp 260f
259:
260:
	jmp 249f
248:
249:
	mov eax, DWORD PTR [ebp+172]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 262f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
264:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 264b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 263f
262:
263:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+172]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+20]
	mov edx, DWORD PTR [esi+24]
	mov ebx, DWORD PTR [esi+28]
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], ecx
	mov DWORD PTR [ebp+8], edx
	mov DWORD PTR [ebp+12], ebx
	mov ebx, ebp
	add ebx, 0
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp]
	mov ecx, DWORD PTR [ebp+4]
	mov edx, DWORD PTR [ebp+8]
	mov ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [ebp+212]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ecx
	mov DWORD PTR [edi+8], edx
	mov DWORD PTR [edi+12], ebx
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2600]
	ret
	.p2align 6

vg_sm4_gcm_open_pclmul:
	lea esp, [esp-2604]
	mov eax, DWORD PTR [esp+2608]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2636]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+2640]
	mov DWORD PTR [esp+36], eax
	mov eax, esp
	add eax, 44
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, ebp
	add esi, 16
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+172], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+212], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+180], eax
	mov eax, 0
	mov DWORD PTR [ebp+188], eax
	mov ecx, 0
	mov ebx, DWORD PTR [ebp+180]
	cmp ebx, 4
	jb 20f
	cmp ebx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test ecx, ecx
	je 24f
	mov eax, DWORD PTR [ebp+192]
	cmp eax, 12
	je 26f
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 28f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 210f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 212f
	jmp 213f
212:
	mov ecx, eax
213:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
214:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 214b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 215f
	jmp 216f
215:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
216:
	jmp 211f
210:
211:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 217f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 218f
217:
218:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 219f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
221:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 221b
	jmp 220f
219:
220:
	jmp 29f
28:
29:
	mov eax, DWORD PTR [ebp+192]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 222f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
224:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 224b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 223f
222:
223:
	mov eax, DWORD PTR [ebp+188]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 27f
26:
	mov edi, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], ecx
	mov DWORD PTR [esi+8], edx
	mov eax, 16777216
	mov DWORD PTR [esi+12], eax
27:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [esi+60], eax
	mov eax, 0
	mov DWORD PTR [esi+16], eax
	mov DWORD PTR [esi+20], eax
	mov DWORD PTR [esi+24], eax
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [ebp+176]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+276], eax
	mov eax, 0
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 225f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 227f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 229f
	jmp 230f
229:
	mov ecx, eax
230:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
231:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 231b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 232f
	jmp 233f
232:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
233:
	jmp 228f
227:
228:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 234f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 235f
234:
235:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 236f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
238:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 238b
	jmp 237f
236:
237:
	jmp 226f
225:
226:
	mov eax, DWORD PTR [ebp+152]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 239f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
241:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 241b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 240f
239:
240:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, 0
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 242f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 244f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 246f
	jmp 247f
246:
	mov ecx, eax
247:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
248:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 248b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 249f
	jmp 250f
249:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
250:
	jmp 245f
244:
245:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 251f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 252f
251:
252:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 253f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
255:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 255b
	jmp 254f
253:
254:
	jmp 243f
242:
243:
	mov eax, DWORD PTR [ebp+172]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 256f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
258:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 258b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 257f
256:
257:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+172]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+20]
	mov edx, DWORD PTR [esi+24]
	mov ebx, DWORD PTR [esi+28]
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], ecx
	mov DWORD PTR [ebp+120], edx
	mov DWORD PTR [ebp+124], ebx
	mov ebx, ebp
	add ebx, 112
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 0
	mov DWORD PTR [ebp+196], eax
	mov DWORD PTR [ebp+200], eax
	mov DWORD PTR [ebp+204], eax
	mov DWORD PTR [ebp+208], eax
	mov edi, DWORD PTR [ebp+212]
	mov edx, ebp
	add edx, 196
	mov ecx, DWORD PTR [ebp+180]
259:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 259b
	mov eax, 0
	mov DWORD PTR [ebp+240], eax
	mov DWORD PTR [ebp+244], eax
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+252], eax
	mov edi, ebp
	add edi, 112
	mov edx, ebp
	add edx, 240
	mov ecx, DWORD PTR [ebp+180]
260:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 260b
	mov eax, DWORD PTR [ebp+240]
	xor eax, DWORD PTR [ebp+196]
	mov ecx, DWORD PTR [ebp+244]
	xor ecx, DWORD PTR [ebp+200]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+248]
	xor ecx, DWORD PTR [ebp+204]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+252]
	xor ecx, DWORD PTR [ebp+208]
	or eax, ecx
	cmp eax, 1
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+184], eax
	test eax, eax
	je 261f
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, 0
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 263f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 265f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 267f
	jmp 268f
267:
	mov ecx, eax
268:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
269:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 269b
	jmp 266f
265:
266:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 270f
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	add edx, 48
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 271f
270:
271:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 272f
	mov eax, 0
	mov DWORD PTR [esi+64], eax
	mov DWORD PTR [esi+68], eax
	mov DWORD PTR [esi+72], eax
	mov DWORD PTR [esi+76], eax
	mov ebx, esi
	add ebx, 64
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	add edx, 48
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	mov ecx, DWORD PTR [ebp+276]
274:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 274b
	jmp 273f
272:
273:
	jmp 264f
263:
264:
	jmp 262f
261:
262:
	mov eax, DWORD PTR [ebp+184]
	jmp 25f
24:
	mov eax, 0
25:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2604]
	ret
	.p2align 6

vg_sm4_gcm_stream_init:
	lea esp, [esp-2584]
	mov eax, DWORD PTR [esp+2588]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2592]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2596]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2600]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+192], eax
	mov eax, 0
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [ebp+192]
	cmp eax, 12
	je 20f
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 22f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 24f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 26f
	jmp 27f
26:
	mov ecx, eax
27:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
28:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 28b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 29f
	jmp 210f
29:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
210:
	jmp 25f
24:
25:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 211f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 212f
211:
212:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 213f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
215:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 215b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov eax, DWORD PTR [ebp+192]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 216f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
218:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 218b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 217f
216:
217:
	mov eax, DWORD PTR [ebp+188]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 21f
20:
	mov edi, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], ecx
	mov DWORD PTR [esi+8], edx
	mov eax, 16777216
	mov DWORD PTR [esi+12], eax
21:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [esi+60], eax
	mov eax, 0
	mov DWORD PTR [esi+16], eax
	mov DWORD PTR [esi+20], eax
	mov DWORD PTR [esi+24], eax
	mov DWORD PTR [esi+28], eax
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2584]
	ret
	.p2align 6

vg_sm4_gcm_stream_aad:
	lea esp, [esp-2592]
	mov eax, DWORD PTR [esp+2596]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2600]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2604]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2608]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [esp+12]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 20f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 22f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 24f
	jmp 25f
24:
	mov ecx, eax
25:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
26:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 26b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 27f
	jmp 28f
27:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
28:
	jmp 23f
22:
23:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 29f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 210f
29:
210:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 211f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
213:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	jmp 212f
211:
212:
	jmp 21f
20:
21:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2592]
	ret
	.p2align 6

vg_sm4_gcm_stream_encrypt:
	lea esp, [esp-2600]
	mov eax, DWORD PTR [esp+2604]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2608]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+32], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+172], eax
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+160]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 20f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 22f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 24f
	jmp 25f
24:
	mov ecx, eax
25:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
26:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 26b
	jmp 23f
22:
23:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 27f
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	add edx, 48
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 28f
27:
28:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 29f
	mov eax, 0
	mov DWORD PTR [esi+64], eax
	mov DWORD PTR [esi+68], eax
	mov DWORD PTR [esi+72], eax
	mov DWORD PTR [esi+76], eax
	mov ebx, esi
	add ebx, 64
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	add edx, 48
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	mov ecx, DWORD PTR [ebp+276]
211:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 211b
	jmp 210f
29:
210:
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebp+172]
	test eax, eax
	je 212f
	mov eax, DWORD PTR [ebp+160]
	or eax, DWORD PTR [ebp+164]
	je 214f
	jmp 215f
214:
	mov eax, DWORD PTR [ebp+152]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 216f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
218:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 218b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 217f
216:
217:
215:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+160]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 219f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 221f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 223f
	jmp 224f
223:
	mov ecx, eax
224:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
225:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 225b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 226f
	jmp 227f
226:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
227:
	jmp 222f
221:
222:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 228f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 229f
228:
229:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 230f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
232:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 232b
	jmp 231f
230:
231:
	jmp 220f
219:
220:
	jmp 213f
212:
213:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2600]
	ret
	.p2align 6

vg_sm4_gcm_stream_decrypt:
	lea esp, [esp-2600]
	mov eax, DWORD PTR [esp+2604]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2608]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+32], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+172], eax
	mov eax, DWORD PTR [ebp+172]
	test eax, eax
	je 20f
	mov eax, DWORD PTR [ebp+160]
	or eax, DWORD PTR [ebp+164]
	je 22f
	jmp 23f
22:
	mov eax, DWORD PTR [ebp+152]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 24f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
26:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 26b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 25f
24:
25:
23:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+160]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 27f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 29f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 211f
	jmp 212f
211:
	mov ecx, eax
212:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
213:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 214f
	jmp 215f
214:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
215:
	jmp 210f
29:
210:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 216f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 217f
216:
217:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 218f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
220:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 220b
	jmp 219f
218:
219:
	jmp 28f
27:
28:
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+160]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 221f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 223f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 225f
	jmp 226f
225:
	mov ecx, eax
226:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
227:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 227b
	jmp 224f
223:
224:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 228f
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	add edx, 48
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 229f
228:
229:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 230f
	mov eax, 0
	mov DWORD PTR [esi+64], eax
	mov DWORD PTR [esi+68], eax
	mov DWORD PTR [esi+72], eax
	mov DWORD PTR [esi+76], eax
	mov ebx, esi
	add ebx, 64
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	add edx, 48
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	mov ecx, DWORD PTR [ebp+276]
232:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 232b
	jmp 231f
230:
231:
	jmp 222f
221:
222:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2600]
	ret
	.p2align 6

vg_sm4_gcm_stream_finish:
	lea esp, [esp-2596]
	mov eax, DWORD PTR [esp+2600]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2604]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2608]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+212], eax
	mov eax, DWORD PTR [ebp+160]
	mov ecx, DWORD PTR [ebp+152]
	mov edx, DWORD PTR [ebp+160]
	or edx, DWORD PTR [ebp+164]
	je 20f
	jmp 21f
20:
	mov eax, ecx
21:
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 22f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
24:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 24b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 23f
22:
23:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+156]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+160]
	mov ecx, DWORD PTR [ebp+164]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+20]
	mov edx, DWORD PTR [esi+24]
	mov ebx, DWORD PTR [esi+28]
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], ecx
	mov DWORD PTR [ebp+8], edx
	mov DWORD PTR [ebp+12], ebx
	mov ebx, ebp
	add ebx, 0
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp]
	mov ecx, DWORD PTR [ebp+4]
	mov edx, DWORD PTR [ebp+8]
	mov ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [ebp+212]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ecx
	mov DWORD PTR [edi+8], edx
	mov DWORD PTR [edi+12], ebx
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2596]
	ret
	.p2align 6

vg_sm4_gcm_stream_verify:
	lea esp, [esp-2600]
	mov eax, DWORD PTR [esp+2604]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2608]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+32], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+212], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+180], eax
	mov ecx, 0
	mov ebx, DWORD PTR [ebp+180]
	cmp ebx, 4
	jb 20f
	cmp ebx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test ecx, ecx
	je 24f
	mov eax, 0
	mov DWORD PTR [ebp+196], eax
	mov DWORD PTR [ebp+200], eax
	mov DWORD PTR [ebp+204], eax
	mov DWORD PTR [ebp+208], eax
	mov edi, DWORD PTR [ebp+212]
	mov edx, ebp
	add edx, 196
	mov ecx, DWORD PTR [ebp+180]
26:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 26b
	mov eax, DWORD PTR [ebp+160]
	mov ecx, DWORD PTR [ebp+152]
	mov edx, DWORD PTR [ebp+160]
	or edx, DWORD PTR [ebp+164]
	je 27f
	jmp 28f
27:
	mov eax, ecx
28:
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 29f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
211:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 211b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 210f
29:
210:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+156]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+160]
	mov ecx, DWORD PTR [ebp+164]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+20]
	mov edx, DWORD PTR [esi+24]
	mov ebx, DWORD PTR [esi+28]
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], ecx
	mov DWORD PTR [ebp+8], edx
	mov DWORD PTR [ebp+12], ebx
	mov ebx, ebp
	add ebx, 0
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 0
	mov DWORD PTR [ebp+240], eax
	mov DWORD PTR [ebp+244], eax
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+252], eax
	mov edi, ebp
	add edi, 0
	mov edx, ebp
	add edx, 240
	mov ecx, DWORD PTR [ebp+180]
212:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 212b
	mov eax, DWORD PTR [ebp+240]
	xor eax, DWORD PTR [ebp+196]
	mov ecx, DWORD PTR [ebp+244]
	xor ecx, DWORD PTR [ebp+200]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+248]
	xor ecx, DWORD PTR [ebp+204]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+252]
	xor ecx, DWORD PTR [ebp+208]
	or eax, ecx
	cmp eax, 1
	mov eax, 0
	adc eax, 0
	jmp 25f
24:
	mov eax, 0
25:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2600]
	ret
	.p2align 6

vg_sm4_gcm_seal:
	lea esp, [esp-2600]
	mov eax, DWORD PTR [esp+2604]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2608]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+32], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, ebp
	add esi, 16
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+172], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+212], eax
	mov eax, 0
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [ebp+192]
	cmp eax, 12
	je 20f
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 22f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 24f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 26f
	jmp 27f
26:
	mov ecx, eax
27:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
28:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 28b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 29f
	jmp 210f
29:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
210:
	jmp 25f
24:
25:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 211f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 212f
211:
212:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 213f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
215:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 215b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov eax, DWORD PTR [ebp+192]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 216f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
218:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 218b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 217f
216:
217:
	mov eax, DWORD PTR [ebp+188]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 21f
20:
	mov edi, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], ecx
	mov DWORD PTR [esi+8], edx
	mov eax, 16777216
	mov DWORD PTR [esi+12], eax
21:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [esi+60], eax
	mov eax, 0
	mov DWORD PTR [esi+16], eax
	mov DWORD PTR [esi+20], eax
	mov DWORD PTR [esi+24], eax
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [ebp+176]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+276], eax
	mov eax, 0
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 219f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 221f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 223f
	jmp 224f
223:
	mov ecx, eax
224:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
225:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 225b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 226f
	jmp 227f
226:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
227:
	jmp 222f
221:
222:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 228f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 229f
228:
229:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 230f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
232:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 232b
	jmp 231f
230:
231:
	jmp 220f
219:
220:
	mov eax, DWORD PTR [ebp+152]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 233f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
235:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 235b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 234f
233:
234:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, 0
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 236f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 238f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 240f
	jmp 241f
240:
	mov ecx, eax
241:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
242:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 242b
	jmp 239f
238:
239:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 243f
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	add edx, 48
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 244f
243:
244:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 245f
	mov eax, 0
	mov DWORD PTR [esi+64], eax
	mov DWORD PTR [esi+68], eax
	mov DWORD PTR [esi+72], eax
	mov DWORD PTR [esi+76], eax
	mov ebx, esi
	add ebx, 64
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	add edx, 48
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	mov ecx, DWORD PTR [ebp+276]
247:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 247b
	jmp 246f
245:
246:
	jmp 237f
236:
237:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, 0
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 248f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 250f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 252f
	jmp 253f
252:
	mov ecx, eax
253:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
254:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 254b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 255f
	jmp 256f
255:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
256:
	jmp 251f
250:
251:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 257f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 258f
257:
258:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 259f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
261:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 261b
	jmp 260f
259:
260:
	jmp 249f
248:
249:
	mov eax, DWORD PTR [ebp+172]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 262f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
264:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 264b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 263f
262:
263:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+172]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+20]
	mov edx, DWORD PTR [esi+24]
	mov ebx, DWORD PTR [esi+28]
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], ecx
	mov DWORD PTR [ebp+8], edx
	mov DWORD PTR [ebp+12], ebx
	mov ebx, ebp
	add ebx, 0
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp]
	mov ecx, DWORD PTR [ebp+4]
	mov edx, DWORD PTR [ebp+8]
	mov ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [ebp+212]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ecx
	mov DWORD PTR [edi+8], edx
	mov DWORD PTR [edi+12], ebx
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2600]
	ret
	.p2align 6

vg_sm4_gcm_open:
	lea esp, [esp-2604]
	mov eax, DWORD PTR [esp+2608]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2636]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+2640]
	mov DWORD PTR [esp+36], eax
	mov eax, esp
	add eax, 44
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, ebp
	add esi, 16
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+172], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+212], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+180], eax
	mov eax, 0
	mov DWORD PTR [ebp+188], eax
	mov ecx, 0
	mov ebx, DWORD PTR [ebp+180]
	cmp ebx, 4
	jb 20f
	cmp ebx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test ecx, ecx
	je 24f
	mov eax, DWORD PTR [ebp+192]
	cmp eax, 12
	je 26f
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 28f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 210f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 212f
	jmp 213f
212:
	mov ecx, eax
213:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
214:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 214b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 215f
	jmp 216f
215:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
216:
	jmp 211f
210:
211:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 217f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 218f
217:
218:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 219f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
221:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 221b
	jmp 220f
219:
220:
	jmp 29f
28:
29:
	mov eax, DWORD PTR [ebp+192]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 222f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
224:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 224b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 223f
222:
223:
	mov eax, DWORD PTR [ebp+188]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 27f
26:
	mov edi, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], ecx
	mov DWORD PTR [esi+8], edx
	mov eax, 16777216
	mov DWORD PTR [esi+12], eax
27:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [esi+60], eax
	mov eax, 0
	mov DWORD PTR [esi+16], eax
	mov DWORD PTR [esi+20], eax
	mov DWORD PTR [esi+24], eax
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [ebp+176]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+276], eax
	mov eax, 0
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 225f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 227f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 229f
	jmp 230f
229:
	mov ecx, eax
230:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
231:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 231b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 232f
	jmp 233f
232:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
233:
	jmp 228f
227:
228:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 234f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 235f
234:
235:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 236f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
238:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 238b
	jmp 237f
236:
237:
	jmp 226f
225:
226:
	mov eax, DWORD PTR [ebp+152]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 239f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
241:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 241b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 240f
239:
240:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, 0
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 242f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 244f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 246f
	jmp 247f
246:
	mov ecx, eax
247:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
248:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 248b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 249f
	jmp 250f
249:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
250:
	jmp 245f
244:
245:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 251f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 252f
251:
252:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 253f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
255:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 255b
	jmp 254f
253:
254:
	jmp 243f
242:
243:
	mov eax, DWORD PTR [ebp+172]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 256f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
258:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 258b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 257f
256:
257:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+172]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+20]
	mov edx, DWORD PTR [esi+24]
	mov ebx, DWORD PTR [esi+28]
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], ecx
	mov DWORD PTR [ebp+120], edx
	mov DWORD PTR [ebp+124], ebx
	mov ebx, ebp
	add ebx, 112
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 0
	mov DWORD PTR [ebp+196], eax
	mov DWORD PTR [ebp+200], eax
	mov DWORD PTR [ebp+204], eax
	mov DWORD PTR [ebp+208], eax
	mov edi, DWORD PTR [ebp+212]
	mov edx, ebp
	add edx, 196
	mov ecx, DWORD PTR [ebp+180]
259:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 259b
	mov eax, 0
	mov DWORD PTR [ebp+240], eax
	mov DWORD PTR [ebp+244], eax
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+252], eax
	mov edi, ebp
	add edi, 112
	mov edx, ebp
	add edx, 240
	mov ecx, DWORD PTR [ebp+180]
260:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 260b
	mov eax, DWORD PTR [ebp+240]
	xor eax, DWORD PTR [ebp+196]
	mov ecx, DWORD PTR [ebp+244]
	xor ecx, DWORD PTR [ebp+200]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+248]
	xor ecx, DWORD PTR [ebp+204]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+252]
	xor ecx, DWORD PTR [ebp+208]
	or eax, ecx
	cmp eax, 1
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+184], eax
	test eax, eax
	je 261f
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, 0
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 263f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 265f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 267f
	jmp 268f
267:
	mov ecx, eax
268:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
269:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 269b
	jmp 266f
265:
266:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 270f
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	add edx, 48
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 271f
270:
271:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 272f
	mov eax, 0
	mov DWORD PTR [esi+64], eax
	mov DWORD PTR [esi+68], eax
	mov DWORD PTR [esi+72], eax
	mov DWORD PTR [esi+76], eax
	mov ebx, esi
	add ebx, 64
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov edx, esi
	add edx, 48
	push edi
	push ebx
	push edx
	push eax
	call {vg_sm4_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	mov ecx, DWORD PTR [ebp+276]
274:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 274b
	jmp 273f
272:
273:
	jmp 264f
263:
264:
	jmp 262f
261:
262:
	mov eax, DWORD PTR [ebp+184]
	jmp 25f
24:
	mov eax, 0
25:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2604]
	ret
	.p2align 6
