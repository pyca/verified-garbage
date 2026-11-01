// The functions of `src/internal/vg_argon2_compress.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_argon2_compress:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+2048], esi
	mov esi, eax
	mov ecx, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ecx]
	xor eax, DWORD PTR [edx]
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+1024], eax
	mov eax, DWORD PTR [ecx+4]
	xor eax, DWORD PTR [edx+4]
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+1028], eax
	mov eax, DWORD PTR [ecx+8]
	xor eax, DWORD PTR [edx+8]
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+1032], eax
	mov eax, DWORD PTR [ecx+12]
	xor eax, DWORD PTR [edx+12]
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+1036], eax
	mov eax, DWORD PTR [ecx+16]
	xor eax, DWORD PTR [edx+16]
	mov DWORD PTR [esi+16], eax
	mov DWORD PTR [esi+1040], eax
	mov eax, DWORD PTR [ecx+20]
	xor eax, DWORD PTR [edx+20]
	mov DWORD PTR [esi+20], eax
	mov DWORD PTR [esi+1044], eax
	mov eax, DWORD PTR [ecx+24]
	xor eax, DWORD PTR [edx+24]
	mov DWORD PTR [esi+24], eax
	mov DWORD PTR [esi+1048], eax
	mov eax, DWORD PTR [ecx+28]
	xor eax, DWORD PTR [edx+28]
	mov DWORD PTR [esi+28], eax
	mov DWORD PTR [esi+1052], eax
	mov eax, DWORD PTR [ecx+32]
	xor eax, DWORD PTR [edx+32]
	mov DWORD PTR [esi+32], eax
	mov DWORD PTR [esi+1056], eax
	mov eax, DWORD PTR [ecx+36]
	xor eax, DWORD PTR [edx+36]
	mov DWORD PTR [esi+36], eax
	mov DWORD PTR [esi+1060], eax
	mov eax, DWORD PTR [ecx+40]
	xor eax, DWORD PTR [edx+40]
	mov DWORD PTR [esi+40], eax
	mov DWORD PTR [esi+1064], eax
	mov eax, DWORD PTR [ecx+44]
	xor eax, DWORD PTR [edx+44]
	mov DWORD PTR [esi+44], eax
	mov DWORD PTR [esi+1068], eax
	mov eax, DWORD PTR [ecx+48]
	xor eax, DWORD PTR [edx+48]
	mov DWORD PTR [esi+48], eax
	mov DWORD PTR [esi+1072], eax
	mov eax, DWORD PTR [ecx+52]
	xor eax, DWORD PTR [edx+52]
	mov DWORD PTR [esi+52], eax
	mov DWORD PTR [esi+1076], eax
	mov eax, DWORD PTR [ecx+56]
	xor eax, DWORD PTR [edx+56]
	mov DWORD PTR [esi+56], eax
	mov DWORD PTR [esi+1080], eax
	mov eax, DWORD PTR [ecx+60]
	xor eax, DWORD PTR [edx+60]
	mov DWORD PTR [esi+60], eax
	mov DWORD PTR [esi+1084], eax
	mov eax, DWORD PTR [ecx+64]
	xor eax, DWORD PTR [edx+64]
	mov DWORD PTR [esi+64], eax
	mov DWORD PTR [esi+1088], eax
	mov eax, DWORD PTR [ecx+68]
	xor eax, DWORD PTR [edx+68]
	mov DWORD PTR [esi+68], eax
	mov DWORD PTR [esi+1092], eax
	mov eax, DWORD PTR [ecx+72]
	xor eax, DWORD PTR [edx+72]
	mov DWORD PTR [esi+72], eax
	mov DWORD PTR [esi+1096], eax
	mov eax, DWORD PTR [ecx+76]
	xor eax, DWORD PTR [edx+76]
	mov DWORD PTR [esi+76], eax
	mov DWORD PTR [esi+1100], eax
	mov eax, DWORD PTR [ecx+80]
	xor eax, DWORD PTR [edx+80]
	mov DWORD PTR [esi+80], eax
	mov DWORD PTR [esi+1104], eax
	mov eax, DWORD PTR [ecx+84]
	xor eax, DWORD PTR [edx+84]
	mov DWORD PTR [esi+84], eax
	mov DWORD PTR [esi+1108], eax
	mov eax, DWORD PTR [ecx+88]
	xor eax, DWORD PTR [edx+88]
	mov DWORD PTR [esi+88], eax
	mov DWORD PTR [esi+1112], eax
	mov eax, DWORD PTR [ecx+92]
	xor eax, DWORD PTR [edx+92]
	mov DWORD PTR [esi+92], eax
	mov DWORD PTR [esi+1116], eax
	mov eax, DWORD PTR [ecx+96]
	xor eax, DWORD PTR [edx+96]
	mov DWORD PTR [esi+96], eax
	mov DWORD PTR [esi+1120], eax
	mov eax, DWORD PTR [ecx+100]
	xor eax, DWORD PTR [edx+100]
	mov DWORD PTR [esi+100], eax
	mov DWORD PTR [esi+1124], eax
	mov eax, DWORD PTR [ecx+104]
	xor eax, DWORD PTR [edx+104]
	mov DWORD PTR [esi+104], eax
	mov DWORD PTR [esi+1128], eax
	mov eax, DWORD PTR [ecx+108]
	xor eax, DWORD PTR [edx+108]
	mov DWORD PTR [esi+108], eax
	mov DWORD PTR [esi+1132], eax
	mov eax, DWORD PTR [ecx+112]
	xor eax, DWORD PTR [edx+112]
	mov DWORD PTR [esi+112], eax
	mov DWORD PTR [esi+1136], eax
	mov eax, DWORD PTR [ecx+116]
	xor eax, DWORD PTR [edx+116]
	mov DWORD PTR [esi+116], eax
	mov DWORD PTR [esi+1140], eax
	mov eax, DWORD PTR [ecx+120]
	xor eax, DWORD PTR [edx+120]
	mov DWORD PTR [esi+120], eax
	mov DWORD PTR [esi+1144], eax
	mov eax, DWORD PTR [ecx+124]
	xor eax, DWORD PTR [edx+124]
	mov DWORD PTR [esi+124], eax
	mov DWORD PTR [esi+1148], eax
	mov eax, DWORD PTR [ecx+128]
	xor eax, DWORD PTR [edx+128]
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+1152], eax
	mov eax, DWORD PTR [ecx+132]
	xor eax, DWORD PTR [edx+132]
	mov DWORD PTR [esi+132], eax
	mov DWORD PTR [esi+1156], eax
	mov eax, DWORD PTR [ecx+136]
	xor eax, DWORD PTR [edx+136]
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+1160], eax
	mov eax, DWORD PTR [ecx+140]
	xor eax, DWORD PTR [edx+140]
	mov DWORD PTR [esi+140], eax
	mov DWORD PTR [esi+1164], eax
	mov eax, DWORD PTR [ecx+144]
	xor eax, DWORD PTR [edx+144]
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+1168], eax
	mov eax, DWORD PTR [ecx+148]
	xor eax, DWORD PTR [edx+148]
	mov DWORD PTR [esi+148], eax
	mov DWORD PTR [esi+1172], eax
	mov eax, DWORD PTR [ecx+152]
	xor eax, DWORD PTR [edx+152]
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+1176], eax
	mov eax, DWORD PTR [ecx+156]
	xor eax, DWORD PTR [edx+156]
	mov DWORD PTR [esi+156], eax
	mov DWORD PTR [esi+1180], eax
	mov eax, DWORD PTR [ecx+160]
	xor eax, DWORD PTR [edx+160]
	mov DWORD PTR [esi+160], eax
	mov DWORD PTR [esi+1184], eax
	mov eax, DWORD PTR [ecx+164]
	xor eax, DWORD PTR [edx+164]
	mov DWORD PTR [esi+164], eax
	mov DWORD PTR [esi+1188], eax
	mov eax, DWORD PTR [ecx+168]
	xor eax, DWORD PTR [edx+168]
	mov DWORD PTR [esi+168], eax
	mov DWORD PTR [esi+1192], eax
	mov eax, DWORD PTR [ecx+172]
	xor eax, DWORD PTR [edx+172]
	mov DWORD PTR [esi+172], eax
	mov DWORD PTR [esi+1196], eax
	mov eax, DWORD PTR [ecx+176]
	xor eax, DWORD PTR [edx+176]
	mov DWORD PTR [esi+176], eax
	mov DWORD PTR [esi+1200], eax
	mov eax, DWORD PTR [ecx+180]
	xor eax, DWORD PTR [edx+180]
	mov DWORD PTR [esi+180], eax
	mov DWORD PTR [esi+1204], eax
	mov eax, DWORD PTR [ecx+184]
	xor eax, DWORD PTR [edx+184]
	mov DWORD PTR [esi+184], eax
	mov DWORD PTR [esi+1208], eax
	mov eax, DWORD PTR [ecx+188]
	xor eax, DWORD PTR [edx+188]
	mov DWORD PTR [esi+188], eax
	mov DWORD PTR [esi+1212], eax
	mov eax, DWORD PTR [ecx+192]
	xor eax, DWORD PTR [edx+192]
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+1216], eax
	mov eax, DWORD PTR [ecx+196]
	xor eax, DWORD PTR [edx+196]
	mov DWORD PTR [esi+196], eax
	mov DWORD PTR [esi+1220], eax
	mov eax, DWORD PTR [ecx+200]
	xor eax, DWORD PTR [edx+200]
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+1224], eax
	mov eax, DWORD PTR [ecx+204]
	xor eax, DWORD PTR [edx+204]
	mov DWORD PTR [esi+204], eax
	mov DWORD PTR [esi+1228], eax
	mov eax, DWORD PTR [ecx+208]
	xor eax, DWORD PTR [edx+208]
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+1232], eax
	mov eax, DWORD PTR [ecx+212]
	xor eax, DWORD PTR [edx+212]
	mov DWORD PTR [esi+212], eax
	mov DWORD PTR [esi+1236], eax
	mov eax, DWORD PTR [ecx+216]
	xor eax, DWORD PTR [edx+216]
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+1240], eax
	mov eax, DWORD PTR [ecx+220]
	xor eax, DWORD PTR [edx+220]
	mov DWORD PTR [esi+220], eax
	mov DWORD PTR [esi+1244], eax
	mov eax, DWORD PTR [ecx+224]
	xor eax, DWORD PTR [edx+224]
	mov DWORD PTR [esi+224], eax
	mov DWORD PTR [esi+1248], eax
	mov eax, DWORD PTR [ecx+228]
	xor eax, DWORD PTR [edx+228]
	mov DWORD PTR [esi+228], eax
	mov DWORD PTR [esi+1252], eax
	mov eax, DWORD PTR [ecx+232]
	xor eax, DWORD PTR [edx+232]
	mov DWORD PTR [esi+232], eax
	mov DWORD PTR [esi+1256], eax
	mov eax, DWORD PTR [ecx+236]
	xor eax, DWORD PTR [edx+236]
	mov DWORD PTR [esi+236], eax
	mov DWORD PTR [esi+1260], eax
	mov eax, DWORD PTR [ecx+240]
	xor eax, DWORD PTR [edx+240]
	mov DWORD PTR [esi+240], eax
	mov DWORD PTR [esi+1264], eax
	mov eax, DWORD PTR [ecx+244]
	xor eax, DWORD PTR [edx+244]
	mov DWORD PTR [esi+244], eax
	mov DWORD PTR [esi+1268], eax
	mov eax, DWORD PTR [ecx+248]
	xor eax, DWORD PTR [edx+248]
	mov DWORD PTR [esi+248], eax
	mov DWORD PTR [esi+1272], eax
	mov eax, DWORD PTR [ecx+252]
	xor eax, DWORD PTR [edx+252]
	mov DWORD PTR [esi+252], eax
	mov DWORD PTR [esi+1276], eax
	mov eax, DWORD PTR [ecx+256]
	xor eax, DWORD PTR [edx+256]
	mov DWORD PTR [esi+256], eax
	mov DWORD PTR [esi+1280], eax
	mov eax, DWORD PTR [ecx+260]
	xor eax, DWORD PTR [edx+260]
	mov DWORD PTR [esi+260], eax
	mov DWORD PTR [esi+1284], eax
	mov eax, DWORD PTR [ecx+264]
	xor eax, DWORD PTR [edx+264]
	mov DWORD PTR [esi+264], eax
	mov DWORD PTR [esi+1288], eax
	mov eax, DWORD PTR [ecx+268]
	xor eax, DWORD PTR [edx+268]
	mov DWORD PTR [esi+268], eax
	mov DWORD PTR [esi+1292], eax
	mov eax, DWORD PTR [ecx+272]
	xor eax, DWORD PTR [edx+272]
	mov DWORD PTR [esi+272], eax
	mov DWORD PTR [esi+1296], eax
	mov eax, DWORD PTR [ecx+276]
	xor eax, DWORD PTR [edx+276]
	mov DWORD PTR [esi+276], eax
	mov DWORD PTR [esi+1300], eax
	mov eax, DWORD PTR [ecx+280]
	xor eax, DWORD PTR [edx+280]
	mov DWORD PTR [esi+280], eax
	mov DWORD PTR [esi+1304], eax
	mov eax, DWORD PTR [ecx+284]
	xor eax, DWORD PTR [edx+284]
	mov DWORD PTR [esi+284], eax
	mov DWORD PTR [esi+1308], eax
	mov eax, DWORD PTR [ecx+288]
	xor eax, DWORD PTR [edx+288]
	mov DWORD PTR [esi+288], eax
	mov DWORD PTR [esi+1312], eax
	mov eax, DWORD PTR [ecx+292]
	xor eax, DWORD PTR [edx+292]
	mov DWORD PTR [esi+292], eax
	mov DWORD PTR [esi+1316], eax
	mov eax, DWORD PTR [ecx+296]
	xor eax, DWORD PTR [edx+296]
	mov DWORD PTR [esi+296], eax
	mov DWORD PTR [esi+1320], eax
	mov eax, DWORD PTR [ecx+300]
	xor eax, DWORD PTR [edx+300]
	mov DWORD PTR [esi+300], eax
	mov DWORD PTR [esi+1324], eax
	mov eax, DWORD PTR [ecx+304]
	xor eax, DWORD PTR [edx+304]
	mov DWORD PTR [esi+304], eax
	mov DWORD PTR [esi+1328], eax
	mov eax, DWORD PTR [ecx+308]
	xor eax, DWORD PTR [edx+308]
	mov DWORD PTR [esi+308], eax
	mov DWORD PTR [esi+1332], eax
	mov eax, DWORD PTR [ecx+312]
	xor eax, DWORD PTR [edx+312]
	mov DWORD PTR [esi+312], eax
	mov DWORD PTR [esi+1336], eax
	mov eax, DWORD PTR [ecx+316]
	xor eax, DWORD PTR [edx+316]
	mov DWORD PTR [esi+316], eax
	mov DWORD PTR [esi+1340], eax
	mov eax, DWORD PTR [ecx+320]
	xor eax, DWORD PTR [edx+320]
	mov DWORD PTR [esi+320], eax
	mov DWORD PTR [esi+1344], eax
	mov eax, DWORD PTR [ecx+324]
	xor eax, DWORD PTR [edx+324]
	mov DWORD PTR [esi+324], eax
	mov DWORD PTR [esi+1348], eax
	mov eax, DWORD PTR [ecx+328]
	xor eax, DWORD PTR [edx+328]
	mov DWORD PTR [esi+328], eax
	mov DWORD PTR [esi+1352], eax
	mov eax, DWORD PTR [ecx+332]
	xor eax, DWORD PTR [edx+332]
	mov DWORD PTR [esi+332], eax
	mov DWORD PTR [esi+1356], eax
	mov eax, DWORD PTR [ecx+336]
	xor eax, DWORD PTR [edx+336]
	mov DWORD PTR [esi+336], eax
	mov DWORD PTR [esi+1360], eax
	mov eax, DWORD PTR [ecx+340]
	xor eax, DWORD PTR [edx+340]
	mov DWORD PTR [esi+340], eax
	mov DWORD PTR [esi+1364], eax
	mov eax, DWORD PTR [ecx+344]
	xor eax, DWORD PTR [edx+344]
	mov DWORD PTR [esi+344], eax
	mov DWORD PTR [esi+1368], eax
	mov eax, DWORD PTR [ecx+348]
	xor eax, DWORD PTR [edx+348]
	mov DWORD PTR [esi+348], eax
	mov DWORD PTR [esi+1372], eax
	mov eax, DWORD PTR [ecx+352]
	xor eax, DWORD PTR [edx+352]
	mov DWORD PTR [esi+352], eax
	mov DWORD PTR [esi+1376], eax
	mov eax, DWORD PTR [ecx+356]
	xor eax, DWORD PTR [edx+356]
	mov DWORD PTR [esi+356], eax
	mov DWORD PTR [esi+1380], eax
	mov eax, DWORD PTR [ecx+360]
	xor eax, DWORD PTR [edx+360]
	mov DWORD PTR [esi+360], eax
	mov DWORD PTR [esi+1384], eax
	mov eax, DWORD PTR [ecx+364]
	xor eax, DWORD PTR [edx+364]
	mov DWORD PTR [esi+364], eax
	mov DWORD PTR [esi+1388], eax
	mov eax, DWORD PTR [ecx+368]
	xor eax, DWORD PTR [edx+368]
	mov DWORD PTR [esi+368], eax
	mov DWORD PTR [esi+1392], eax
	mov eax, DWORD PTR [ecx+372]
	xor eax, DWORD PTR [edx+372]
	mov DWORD PTR [esi+372], eax
	mov DWORD PTR [esi+1396], eax
	mov eax, DWORD PTR [ecx+376]
	xor eax, DWORD PTR [edx+376]
	mov DWORD PTR [esi+376], eax
	mov DWORD PTR [esi+1400], eax
	mov eax, DWORD PTR [ecx+380]
	xor eax, DWORD PTR [edx+380]
	mov DWORD PTR [esi+380], eax
	mov DWORD PTR [esi+1404], eax
	mov eax, DWORD PTR [ecx+384]
	xor eax, DWORD PTR [edx+384]
	mov DWORD PTR [esi+384], eax
	mov DWORD PTR [esi+1408], eax
	mov eax, DWORD PTR [ecx+388]
	xor eax, DWORD PTR [edx+388]
	mov DWORD PTR [esi+388], eax
	mov DWORD PTR [esi+1412], eax
	mov eax, DWORD PTR [ecx+392]
	xor eax, DWORD PTR [edx+392]
	mov DWORD PTR [esi+392], eax
	mov DWORD PTR [esi+1416], eax
	mov eax, DWORD PTR [ecx+396]
	xor eax, DWORD PTR [edx+396]
	mov DWORD PTR [esi+396], eax
	mov DWORD PTR [esi+1420], eax
	mov eax, DWORD PTR [ecx+400]
	xor eax, DWORD PTR [edx+400]
	mov DWORD PTR [esi+400], eax
	mov DWORD PTR [esi+1424], eax
	mov eax, DWORD PTR [ecx+404]
	xor eax, DWORD PTR [edx+404]
	mov DWORD PTR [esi+404], eax
	mov DWORD PTR [esi+1428], eax
	mov eax, DWORD PTR [ecx+408]
	xor eax, DWORD PTR [edx+408]
	mov DWORD PTR [esi+408], eax
	mov DWORD PTR [esi+1432], eax
	mov eax, DWORD PTR [ecx+412]
	xor eax, DWORD PTR [edx+412]
	mov DWORD PTR [esi+412], eax
	mov DWORD PTR [esi+1436], eax
	mov eax, DWORD PTR [ecx+416]
	xor eax, DWORD PTR [edx+416]
	mov DWORD PTR [esi+416], eax
	mov DWORD PTR [esi+1440], eax
	mov eax, DWORD PTR [ecx+420]
	xor eax, DWORD PTR [edx+420]
	mov DWORD PTR [esi+420], eax
	mov DWORD PTR [esi+1444], eax
	mov eax, DWORD PTR [ecx+424]
	xor eax, DWORD PTR [edx+424]
	mov DWORD PTR [esi+424], eax
	mov DWORD PTR [esi+1448], eax
	mov eax, DWORD PTR [ecx+428]
	xor eax, DWORD PTR [edx+428]
	mov DWORD PTR [esi+428], eax
	mov DWORD PTR [esi+1452], eax
	mov eax, DWORD PTR [ecx+432]
	xor eax, DWORD PTR [edx+432]
	mov DWORD PTR [esi+432], eax
	mov DWORD PTR [esi+1456], eax
	mov eax, DWORD PTR [ecx+436]
	xor eax, DWORD PTR [edx+436]
	mov DWORD PTR [esi+436], eax
	mov DWORD PTR [esi+1460], eax
	mov eax, DWORD PTR [ecx+440]
	xor eax, DWORD PTR [edx+440]
	mov DWORD PTR [esi+440], eax
	mov DWORD PTR [esi+1464], eax
	mov eax, DWORD PTR [ecx+444]
	xor eax, DWORD PTR [edx+444]
	mov DWORD PTR [esi+444], eax
	mov DWORD PTR [esi+1468], eax
	mov eax, DWORD PTR [ecx+448]
	xor eax, DWORD PTR [edx+448]
	mov DWORD PTR [esi+448], eax
	mov DWORD PTR [esi+1472], eax
	mov eax, DWORD PTR [ecx+452]
	xor eax, DWORD PTR [edx+452]
	mov DWORD PTR [esi+452], eax
	mov DWORD PTR [esi+1476], eax
	mov eax, DWORD PTR [ecx+456]
	xor eax, DWORD PTR [edx+456]
	mov DWORD PTR [esi+456], eax
	mov DWORD PTR [esi+1480], eax
	mov eax, DWORD PTR [ecx+460]
	xor eax, DWORD PTR [edx+460]
	mov DWORD PTR [esi+460], eax
	mov DWORD PTR [esi+1484], eax
	mov eax, DWORD PTR [ecx+464]
	xor eax, DWORD PTR [edx+464]
	mov DWORD PTR [esi+464], eax
	mov DWORD PTR [esi+1488], eax
	mov eax, DWORD PTR [ecx+468]
	xor eax, DWORD PTR [edx+468]
	mov DWORD PTR [esi+468], eax
	mov DWORD PTR [esi+1492], eax
	mov eax, DWORD PTR [ecx+472]
	xor eax, DWORD PTR [edx+472]
	mov DWORD PTR [esi+472], eax
	mov DWORD PTR [esi+1496], eax
	mov eax, DWORD PTR [ecx+476]
	xor eax, DWORD PTR [edx+476]
	mov DWORD PTR [esi+476], eax
	mov DWORD PTR [esi+1500], eax
	mov eax, DWORD PTR [ecx+480]
	xor eax, DWORD PTR [edx+480]
	mov DWORD PTR [esi+480], eax
	mov DWORD PTR [esi+1504], eax
	mov eax, DWORD PTR [ecx+484]
	xor eax, DWORD PTR [edx+484]
	mov DWORD PTR [esi+484], eax
	mov DWORD PTR [esi+1508], eax
	mov eax, DWORD PTR [ecx+488]
	xor eax, DWORD PTR [edx+488]
	mov DWORD PTR [esi+488], eax
	mov DWORD PTR [esi+1512], eax
	mov eax, DWORD PTR [ecx+492]
	xor eax, DWORD PTR [edx+492]
	mov DWORD PTR [esi+492], eax
	mov DWORD PTR [esi+1516], eax
	mov eax, DWORD PTR [ecx+496]
	xor eax, DWORD PTR [edx+496]
	mov DWORD PTR [esi+496], eax
	mov DWORD PTR [esi+1520], eax
	mov eax, DWORD PTR [ecx+500]
	xor eax, DWORD PTR [edx+500]
	mov DWORD PTR [esi+500], eax
	mov DWORD PTR [esi+1524], eax
	mov eax, DWORD PTR [ecx+504]
	xor eax, DWORD PTR [edx+504]
	mov DWORD PTR [esi+504], eax
	mov DWORD PTR [esi+1528], eax
	mov eax, DWORD PTR [ecx+508]
	xor eax, DWORD PTR [edx+508]
	mov DWORD PTR [esi+508], eax
	mov DWORD PTR [esi+1532], eax
	mov eax, DWORD PTR [ecx+512]
	xor eax, DWORD PTR [edx+512]
	mov DWORD PTR [esi+512], eax
	mov DWORD PTR [esi+1536], eax
	mov eax, DWORD PTR [ecx+516]
	xor eax, DWORD PTR [edx+516]
	mov DWORD PTR [esi+516], eax
	mov DWORD PTR [esi+1540], eax
	mov eax, DWORD PTR [ecx+520]
	xor eax, DWORD PTR [edx+520]
	mov DWORD PTR [esi+520], eax
	mov DWORD PTR [esi+1544], eax
	mov eax, DWORD PTR [ecx+524]
	xor eax, DWORD PTR [edx+524]
	mov DWORD PTR [esi+524], eax
	mov DWORD PTR [esi+1548], eax
	mov eax, DWORD PTR [ecx+528]
	xor eax, DWORD PTR [edx+528]
	mov DWORD PTR [esi+528], eax
	mov DWORD PTR [esi+1552], eax
	mov eax, DWORD PTR [ecx+532]
	xor eax, DWORD PTR [edx+532]
	mov DWORD PTR [esi+532], eax
	mov DWORD PTR [esi+1556], eax
	mov eax, DWORD PTR [ecx+536]
	xor eax, DWORD PTR [edx+536]
	mov DWORD PTR [esi+536], eax
	mov DWORD PTR [esi+1560], eax
	mov eax, DWORD PTR [ecx+540]
	xor eax, DWORD PTR [edx+540]
	mov DWORD PTR [esi+540], eax
	mov DWORD PTR [esi+1564], eax
	mov eax, DWORD PTR [ecx+544]
	xor eax, DWORD PTR [edx+544]
	mov DWORD PTR [esi+544], eax
	mov DWORD PTR [esi+1568], eax
	mov eax, DWORD PTR [ecx+548]
	xor eax, DWORD PTR [edx+548]
	mov DWORD PTR [esi+548], eax
	mov DWORD PTR [esi+1572], eax
	mov eax, DWORD PTR [ecx+552]
	xor eax, DWORD PTR [edx+552]
	mov DWORD PTR [esi+552], eax
	mov DWORD PTR [esi+1576], eax
	mov eax, DWORD PTR [ecx+556]
	xor eax, DWORD PTR [edx+556]
	mov DWORD PTR [esi+556], eax
	mov DWORD PTR [esi+1580], eax
	mov eax, DWORD PTR [ecx+560]
	xor eax, DWORD PTR [edx+560]
	mov DWORD PTR [esi+560], eax
	mov DWORD PTR [esi+1584], eax
	mov eax, DWORD PTR [ecx+564]
	xor eax, DWORD PTR [edx+564]
	mov DWORD PTR [esi+564], eax
	mov DWORD PTR [esi+1588], eax
	mov eax, DWORD PTR [ecx+568]
	xor eax, DWORD PTR [edx+568]
	mov DWORD PTR [esi+568], eax
	mov DWORD PTR [esi+1592], eax
	mov eax, DWORD PTR [ecx+572]
	xor eax, DWORD PTR [edx+572]
	mov DWORD PTR [esi+572], eax
	mov DWORD PTR [esi+1596], eax
	mov eax, DWORD PTR [ecx+576]
	xor eax, DWORD PTR [edx+576]
	mov DWORD PTR [esi+576], eax
	mov DWORD PTR [esi+1600], eax
	mov eax, DWORD PTR [ecx+580]
	xor eax, DWORD PTR [edx+580]
	mov DWORD PTR [esi+580], eax
	mov DWORD PTR [esi+1604], eax
	mov eax, DWORD PTR [ecx+584]
	xor eax, DWORD PTR [edx+584]
	mov DWORD PTR [esi+584], eax
	mov DWORD PTR [esi+1608], eax
	mov eax, DWORD PTR [ecx+588]
	xor eax, DWORD PTR [edx+588]
	mov DWORD PTR [esi+588], eax
	mov DWORD PTR [esi+1612], eax
	mov eax, DWORD PTR [ecx+592]
	xor eax, DWORD PTR [edx+592]
	mov DWORD PTR [esi+592], eax
	mov DWORD PTR [esi+1616], eax
	mov eax, DWORD PTR [ecx+596]
	xor eax, DWORD PTR [edx+596]
	mov DWORD PTR [esi+596], eax
	mov DWORD PTR [esi+1620], eax
	mov eax, DWORD PTR [ecx+600]
	xor eax, DWORD PTR [edx+600]
	mov DWORD PTR [esi+600], eax
	mov DWORD PTR [esi+1624], eax
	mov eax, DWORD PTR [ecx+604]
	xor eax, DWORD PTR [edx+604]
	mov DWORD PTR [esi+604], eax
	mov DWORD PTR [esi+1628], eax
	mov eax, DWORD PTR [ecx+608]
	xor eax, DWORD PTR [edx+608]
	mov DWORD PTR [esi+608], eax
	mov DWORD PTR [esi+1632], eax
	mov eax, DWORD PTR [ecx+612]
	xor eax, DWORD PTR [edx+612]
	mov DWORD PTR [esi+612], eax
	mov DWORD PTR [esi+1636], eax
	mov eax, DWORD PTR [ecx+616]
	xor eax, DWORD PTR [edx+616]
	mov DWORD PTR [esi+616], eax
	mov DWORD PTR [esi+1640], eax
	mov eax, DWORD PTR [ecx+620]
	xor eax, DWORD PTR [edx+620]
	mov DWORD PTR [esi+620], eax
	mov DWORD PTR [esi+1644], eax
	mov eax, DWORD PTR [ecx+624]
	xor eax, DWORD PTR [edx+624]
	mov DWORD PTR [esi+624], eax
	mov DWORD PTR [esi+1648], eax
	mov eax, DWORD PTR [ecx+628]
	xor eax, DWORD PTR [edx+628]
	mov DWORD PTR [esi+628], eax
	mov DWORD PTR [esi+1652], eax
	mov eax, DWORD PTR [ecx+632]
	xor eax, DWORD PTR [edx+632]
	mov DWORD PTR [esi+632], eax
	mov DWORD PTR [esi+1656], eax
	mov eax, DWORD PTR [ecx+636]
	xor eax, DWORD PTR [edx+636]
	mov DWORD PTR [esi+636], eax
	mov DWORD PTR [esi+1660], eax
	mov eax, DWORD PTR [ecx+640]
	xor eax, DWORD PTR [edx+640]
	mov DWORD PTR [esi+640], eax
	mov DWORD PTR [esi+1664], eax
	mov eax, DWORD PTR [ecx+644]
	xor eax, DWORD PTR [edx+644]
	mov DWORD PTR [esi+644], eax
	mov DWORD PTR [esi+1668], eax
	mov eax, DWORD PTR [ecx+648]
	xor eax, DWORD PTR [edx+648]
	mov DWORD PTR [esi+648], eax
	mov DWORD PTR [esi+1672], eax
	mov eax, DWORD PTR [ecx+652]
	xor eax, DWORD PTR [edx+652]
	mov DWORD PTR [esi+652], eax
	mov DWORD PTR [esi+1676], eax
	mov eax, DWORD PTR [ecx+656]
	xor eax, DWORD PTR [edx+656]
	mov DWORD PTR [esi+656], eax
	mov DWORD PTR [esi+1680], eax
	mov eax, DWORD PTR [ecx+660]
	xor eax, DWORD PTR [edx+660]
	mov DWORD PTR [esi+660], eax
	mov DWORD PTR [esi+1684], eax
	mov eax, DWORD PTR [ecx+664]
	xor eax, DWORD PTR [edx+664]
	mov DWORD PTR [esi+664], eax
	mov DWORD PTR [esi+1688], eax
	mov eax, DWORD PTR [ecx+668]
	xor eax, DWORD PTR [edx+668]
	mov DWORD PTR [esi+668], eax
	mov DWORD PTR [esi+1692], eax
	mov eax, DWORD PTR [ecx+672]
	xor eax, DWORD PTR [edx+672]
	mov DWORD PTR [esi+672], eax
	mov DWORD PTR [esi+1696], eax
	mov eax, DWORD PTR [ecx+676]
	xor eax, DWORD PTR [edx+676]
	mov DWORD PTR [esi+676], eax
	mov DWORD PTR [esi+1700], eax
	mov eax, DWORD PTR [ecx+680]
	xor eax, DWORD PTR [edx+680]
	mov DWORD PTR [esi+680], eax
	mov DWORD PTR [esi+1704], eax
	mov eax, DWORD PTR [ecx+684]
	xor eax, DWORD PTR [edx+684]
	mov DWORD PTR [esi+684], eax
	mov DWORD PTR [esi+1708], eax
	mov eax, DWORD PTR [ecx+688]
	xor eax, DWORD PTR [edx+688]
	mov DWORD PTR [esi+688], eax
	mov DWORD PTR [esi+1712], eax
	mov eax, DWORD PTR [ecx+692]
	xor eax, DWORD PTR [edx+692]
	mov DWORD PTR [esi+692], eax
	mov DWORD PTR [esi+1716], eax
	mov eax, DWORD PTR [ecx+696]
	xor eax, DWORD PTR [edx+696]
	mov DWORD PTR [esi+696], eax
	mov DWORD PTR [esi+1720], eax
	mov eax, DWORD PTR [ecx+700]
	xor eax, DWORD PTR [edx+700]
	mov DWORD PTR [esi+700], eax
	mov DWORD PTR [esi+1724], eax
	mov eax, DWORD PTR [ecx+704]
	xor eax, DWORD PTR [edx+704]
	mov DWORD PTR [esi+704], eax
	mov DWORD PTR [esi+1728], eax
	mov eax, DWORD PTR [ecx+708]
	xor eax, DWORD PTR [edx+708]
	mov DWORD PTR [esi+708], eax
	mov DWORD PTR [esi+1732], eax
	mov eax, DWORD PTR [ecx+712]
	xor eax, DWORD PTR [edx+712]
	mov DWORD PTR [esi+712], eax
	mov DWORD PTR [esi+1736], eax
	mov eax, DWORD PTR [ecx+716]
	xor eax, DWORD PTR [edx+716]
	mov DWORD PTR [esi+716], eax
	mov DWORD PTR [esi+1740], eax
	mov eax, DWORD PTR [ecx+720]
	xor eax, DWORD PTR [edx+720]
	mov DWORD PTR [esi+720], eax
	mov DWORD PTR [esi+1744], eax
	mov eax, DWORD PTR [ecx+724]
	xor eax, DWORD PTR [edx+724]
	mov DWORD PTR [esi+724], eax
	mov DWORD PTR [esi+1748], eax
	mov eax, DWORD PTR [ecx+728]
	xor eax, DWORD PTR [edx+728]
	mov DWORD PTR [esi+728], eax
	mov DWORD PTR [esi+1752], eax
	mov eax, DWORD PTR [ecx+732]
	xor eax, DWORD PTR [edx+732]
	mov DWORD PTR [esi+732], eax
	mov DWORD PTR [esi+1756], eax
	mov eax, DWORD PTR [ecx+736]
	xor eax, DWORD PTR [edx+736]
	mov DWORD PTR [esi+736], eax
	mov DWORD PTR [esi+1760], eax
	mov eax, DWORD PTR [ecx+740]
	xor eax, DWORD PTR [edx+740]
	mov DWORD PTR [esi+740], eax
	mov DWORD PTR [esi+1764], eax
	mov eax, DWORD PTR [ecx+744]
	xor eax, DWORD PTR [edx+744]
	mov DWORD PTR [esi+744], eax
	mov DWORD PTR [esi+1768], eax
	mov eax, DWORD PTR [ecx+748]
	xor eax, DWORD PTR [edx+748]
	mov DWORD PTR [esi+748], eax
	mov DWORD PTR [esi+1772], eax
	mov eax, DWORD PTR [ecx+752]
	xor eax, DWORD PTR [edx+752]
	mov DWORD PTR [esi+752], eax
	mov DWORD PTR [esi+1776], eax
	mov eax, DWORD PTR [ecx+756]
	xor eax, DWORD PTR [edx+756]
	mov DWORD PTR [esi+756], eax
	mov DWORD PTR [esi+1780], eax
	mov eax, DWORD PTR [ecx+760]
	xor eax, DWORD PTR [edx+760]
	mov DWORD PTR [esi+760], eax
	mov DWORD PTR [esi+1784], eax
	mov eax, DWORD PTR [ecx+764]
	xor eax, DWORD PTR [edx+764]
	mov DWORD PTR [esi+764], eax
	mov DWORD PTR [esi+1788], eax
	mov eax, DWORD PTR [ecx+768]
	xor eax, DWORD PTR [edx+768]
	mov DWORD PTR [esi+768], eax
	mov DWORD PTR [esi+1792], eax
	mov eax, DWORD PTR [ecx+772]
	xor eax, DWORD PTR [edx+772]
	mov DWORD PTR [esi+772], eax
	mov DWORD PTR [esi+1796], eax
	mov eax, DWORD PTR [ecx+776]
	xor eax, DWORD PTR [edx+776]
	mov DWORD PTR [esi+776], eax
	mov DWORD PTR [esi+1800], eax
	mov eax, DWORD PTR [ecx+780]
	xor eax, DWORD PTR [edx+780]
	mov DWORD PTR [esi+780], eax
	mov DWORD PTR [esi+1804], eax
	mov eax, DWORD PTR [ecx+784]
	xor eax, DWORD PTR [edx+784]
	mov DWORD PTR [esi+784], eax
	mov DWORD PTR [esi+1808], eax
	mov eax, DWORD PTR [ecx+788]
	xor eax, DWORD PTR [edx+788]
	mov DWORD PTR [esi+788], eax
	mov DWORD PTR [esi+1812], eax
	mov eax, DWORD PTR [ecx+792]
	xor eax, DWORD PTR [edx+792]
	mov DWORD PTR [esi+792], eax
	mov DWORD PTR [esi+1816], eax
	mov eax, DWORD PTR [ecx+796]
	xor eax, DWORD PTR [edx+796]
	mov DWORD PTR [esi+796], eax
	mov DWORD PTR [esi+1820], eax
	mov eax, DWORD PTR [ecx+800]
	xor eax, DWORD PTR [edx+800]
	mov DWORD PTR [esi+800], eax
	mov DWORD PTR [esi+1824], eax
	mov eax, DWORD PTR [ecx+804]
	xor eax, DWORD PTR [edx+804]
	mov DWORD PTR [esi+804], eax
	mov DWORD PTR [esi+1828], eax
	mov eax, DWORD PTR [ecx+808]
	xor eax, DWORD PTR [edx+808]
	mov DWORD PTR [esi+808], eax
	mov DWORD PTR [esi+1832], eax
	mov eax, DWORD PTR [ecx+812]
	xor eax, DWORD PTR [edx+812]
	mov DWORD PTR [esi+812], eax
	mov DWORD PTR [esi+1836], eax
	mov eax, DWORD PTR [ecx+816]
	xor eax, DWORD PTR [edx+816]
	mov DWORD PTR [esi+816], eax
	mov DWORD PTR [esi+1840], eax
	mov eax, DWORD PTR [ecx+820]
	xor eax, DWORD PTR [edx+820]
	mov DWORD PTR [esi+820], eax
	mov DWORD PTR [esi+1844], eax
	mov eax, DWORD PTR [ecx+824]
	xor eax, DWORD PTR [edx+824]
	mov DWORD PTR [esi+824], eax
	mov DWORD PTR [esi+1848], eax
	mov eax, DWORD PTR [ecx+828]
	xor eax, DWORD PTR [edx+828]
	mov DWORD PTR [esi+828], eax
	mov DWORD PTR [esi+1852], eax
	mov eax, DWORD PTR [ecx+832]
	xor eax, DWORD PTR [edx+832]
	mov DWORD PTR [esi+832], eax
	mov DWORD PTR [esi+1856], eax
	mov eax, DWORD PTR [ecx+836]
	xor eax, DWORD PTR [edx+836]
	mov DWORD PTR [esi+836], eax
	mov DWORD PTR [esi+1860], eax
	mov eax, DWORD PTR [ecx+840]
	xor eax, DWORD PTR [edx+840]
	mov DWORD PTR [esi+840], eax
	mov DWORD PTR [esi+1864], eax
	mov eax, DWORD PTR [ecx+844]
	xor eax, DWORD PTR [edx+844]
	mov DWORD PTR [esi+844], eax
	mov DWORD PTR [esi+1868], eax
	mov eax, DWORD PTR [ecx+848]
	xor eax, DWORD PTR [edx+848]
	mov DWORD PTR [esi+848], eax
	mov DWORD PTR [esi+1872], eax
	mov eax, DWORD PTR [ecx+852]
	xor eax, DWORD PTR [edx+852]
	mov DWORD PTR [esi+852], eax
	mov DWORD PTR [esi+1876], eax
	mov eax, DWORD PTR [ecx+856]
	xor eax, DWORD PTR [edx+856]
	mov DWORD PTR [esi+856], eax
	mov DWORD PTR [esi+1880], eax
	mov eax, DWORD PTR [ecx+860]
	xor eax, DWORD PTR [edx+860]
	mov DWORD PTR [esi+860], eax
	mov DWORD PTR [esi+1884], eax
	mov eax, DWORD PTR [ecx+864]
	xor eax, DWORD PTR [edx+864]
	mov DWORD PTR [esi+864], eax
	mov DWORD PTR [esi+1888], eax
	mov eax, DWORD PTR [ecx+868]
	xor eax, DWORD PTR [edx+868]
	mov DWORD PTR [esi+868], eax
	mov DWORD PTR [esi+1892], eax
	mov eax, DWORD PTR [ecx+872]
	xor eax, DWORD PTR [edx+872]
	mov DWORD PTR [esi+872], eax
	mov DWORD PTR [esi+1896], eax
	mov eax, DWORD PTR [ecx+876]
	xor eax, DWORD PTR [edx+876]
	mov DWORD PTR [esi+876], eax
	mov DWORD PTR [esi+1900], eax
	mov eax, DWORD PTR [ecx+880]
	xor eax, DWORD PTR [edx+880]
	mov DWORD PTR [esi+880], eax
	mov DWORD PTR [esi+1904], eax
	mov eax, DWORD PTR [ecx+884]
	xor eax, DWORD PTR [edx+884]
	mov DWORD PTR [esi+884], eax
	mov DWORD PTR [esi+1908], eax
	mov eax, DWORD PTR [ecx+888]
	xor eax, DWORD PTR [edx+888]
	mov DWORD PTR [esi+888], eax
	mov DWORD PTR [esi+1912], eax
	mov eax, DWORD PTR [ecx+892]
	xor eax, DWORD PTR [edx+892]
	mov DWORD PTR [esi+892], eax
	mov DWORD PTR [esi+1916], eax
	mov eax, DWORD PTR [ecx+896]
	xor eax, DWORD PTR [edx+896]
	mov DWORD PTR [esi+896], eax
	mov DWORD PTR [esi+1920], eax
	mov eax, DWORD PTR [ecx+900]
	xor eax, DWORD PTR [edx+900]
	mov DWORD PTR [esi+900], eax
	mov DWORD PTR [esi+1924], eax
	mov eax, DWORD PTR [ecx+904]
	xor eax, DWORD PTR [edx+904]
	mov DWORD PTR [esi+904], eax
	mov DWORD PTR [esi+1928], eax
	mov eax, DWORD PTR [ecx+908]
	xor eax, DWORD PTR [edx+908]
	mov DWORD PTR [esi+908], eax
	mov DWORD PTR [esi+1932], eax
	mov eax, DWORD PTR [ecx+912]
	xor eax, DWORD PTR [edx+912]
	mov DWORD PTR [esi+912], eax
	mov DWORD PTR [esi+1936], eax
	mov eax, DWORD PTR [ecx+916]
	xor eax, DWORD PTR [edx+916]
	mov DWORD PTR [esi+916], eax
	mov DWORD PTR [esi+1940], eax
	mov eax, DWORD PTR [ecx+920]
	xor eax, DWORD PTR [edx+920]
	mov DWORD PTR [esi+920], eax
	mov DWORD PTR [esi+1944], eax
	mov eax, DWORD PTR [ecx+924]
	xor eax, DWORD PTR [edx+924]
	mov DWORD PTR [esi+924], eax
	mov DWORD PTR [esi+1948], eax
	mov eax, DWORD PTR [ecx+928]
	xor eax, DWORD PTR [edx+928]
	mov DWORD PTR [esi+928], eax
	mov DWORD PTR [esi+1952], eax
	mov eax, DWORD PTR [ecx+932]
	xor eax, DWORD PTR [edx+932]
	mov DWORD PTR [esi+932], eax
	mov DWORD PTR [esi+1956], eax
	mov eax, DWORD PTR [ecx+936]
	xor eax, DWORD PTR [edx+936]
	mov DWORD PTR [esi+936], eax
	mov DWORD PTR [esi+1960], eax
	mov eax, DWORD PTR [ecx+940]
	xor eax, DWORD PTR [edx+940]
	mov DWORD PTR [esi+940], eax
	mov DWORD PTR [esi+1964], eax
	mov eax, DWORD PTR [ecx+944]
	xor eax, DWORD PTR [edx+944]
	mov DWORD PTR [esi+944], eax
	mov DWORD PTR [esi+1968], eax
	mov eax, DWORD PTR [ecx+948]
	xor eax, DWORD PTR [edx+948]
	mov DWORD PTR [esi+948], eax
	mov DWORD PTR [esi+1972], eax
	mov eax, DWORD PTR [ecx+952]
	xor eax, DWORD PTR [edx+952]
	mov DWORD PTR [esi+952], eax
	mov DWORD PTR [esi+1976], eax
	mov eax, DWORD PTR [ecx+956]
	xor eax, DWORD PTR [edx+956]
	mov DWORD PTR [esi+956], eax
	mov DWORD PTR [esi+1980], eax
	mov eax, DWORD PTR [ecx+960]
	xor eax, DWORD PTR [edx+960]
	mov DWORD PTR [esi+960], eax
	mov DWORD PTR [esi+1984], eax
	mov eax, DWORD PTR [ecx+964]
	xor eax, DWORD PTR [edx+964]
	mov DWORD PTR [esi+964], eax
	mov DWORD PTR [esi+1988], eax
	mov eax, DWORD PTR [ecx+968]
	xor eax, DWORD PTR [edx+968]
	mov DWORD PTR [esi+968], eax
	mov DWORD PTR [esi+1992], eax
	mov eax, DWORD PTR [ecx+972]
	xor eax, DWORD PTR [edx+972]
	mov DWORD PTR [esi+972], eax
	mov DWORD PTR [esi+1996], eax
	mov eax, DWORD PTR [ecx+976]
	xor eax, DWORD PTR [edx+976]
	mov DWORD PTR [esi+976], eax
	mov DWORD PTR [esi+2000], eax
	mov eax, DWORD PTR [ecx+980]
	xor eax, DWORD PTR [edx+980]
	mov DWORD PTR [esi+980], eax
	mov DWORD PTR [esi+2004], eax
	mov eax, DWORD PTR [ecx+984]
	xor eax, DWORD PTR [edx+984]
	mov DWORD PTR [esi+984], eax
	mov DWORD PTR [esi+2008], eax
	mov eax, DWORD PTR [ecx+988]
	xor eax, DWORD PTR [edx+988]
	mov DWORD PTR [esi+988], eax
	mov DWORD PTR [esi+2012], eax
	mov eax, DWORD PTR [ecx+992]
	xor eax, DWORD PTR [edx+992]
	mov DWORD PTR [esi+992], eax
	mov DWORD PTR [esi+2016], eax
	mov eax, DWORD PTR [ecx+996]
	xor eax, DWORD PTR [edx+996]
	mov DWORD PTR [esi+996], eax
	mov DWORD PTR [esi+2020], eax
	mov eax, DWORD PTR [ecx+1000]
	xor eax, DWORD PTR [edx+1000]
	mov DWORD PTR [esi+1000], eax
	mov DWORD PTR [esi+2024], eax
	mov eax, DWORD PTR [ecx+1004]
	xor eax, DWORD PTR [edx+1004]
	mov DWORD PTR [esi+1004], eax
	mov DWORD PTR [esi+2028], eax
	mov eax, DWORD PTR [ecx+1008]
	xor eax, DWORD PTR [edx+1008]
	mov DWORD PTR [esi+1008], eax
	mov DWORD PTR [esi+2032], eax
	mov eax, DWORD PTR [ecx+1012]
	xor eax, DWORD PTR [edx+1012]
	mov DWORD PTR [esi+1012], eax
	mov DWORD PTR [esi+2036], eax
	mov eax, DWORD PTR [ecx+1016]
	xor eax, DWORD PTR [edx+1016]
	mov DWORD PTR [esi+1016], eax
	mov DWORD PTR [esi+2040], eax
	mov eax, DWORD PTR [ecx+1020]
	xor eax, DWORD PTR [edx+1020]
	mov DWORD PTR [esi+1020], eax
	mov DWORD PTR [esi+2044], eax
	mov edx, DWORD PTR [esi+1056]
	mov eax, DWORD PTR [esi+1024]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1056]
	adc edx, DWORD PTR [esi+1060]
	add eax, DWORD PTR [esi+1024]
	adc edx, DWORD PTR [esi+1028]
	mov DWORD PTR [esi+1024], eax
	mov DWORD PTR [esi+1028], edx
	mov eax, DWORD PTR [esi+1120]
	mov edx, DWORD PTR [esi+1124]
	xor eax, DWORD PTR [esi+1024]
	xor edx, DWORD PTR [esi+1028]
	mov DWORD PTR [esi+1120], edx
	mov DWORD PTR [esi+1124], eax
	mov edx, DWORD PTR [esi+1120]
	mov eax, DWORD PTR [esi+1088]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1120]
	adc edx, DWORD PTR [esi+1124]
	add eax, DWORD PTR [esi+1088]
	adc edx, DWORD PTR [esi+1092]
	mov DWORD PTR [esi+1088], eax
	mov DWORD PTR [esi+1092], edx
	mov eax, DWORD PTR [esi+1056]
	mov edx, DWORD PTR [esi+1060]
	xor eax, DWORD PTR [esi+1088]
	xor edx, DWORD PTR [esi+1092]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1056], edx
	mov DWORD PTR [esi+1060], eax
	mov edx, DWORD PTR [esi+1056]
	mov eax, DWORD PTR [esi+1024]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1056]
	adc edx, DWORD PTR [esi+1060]
	add eax, DWORD PTR [esi+1024]
	adc edx, DWORD PTR [esi+1028]
	mov DWORD PTR [esi+1024], eax
	mov DWORD PTR [esi+1028], edx
	mov eax, DWORD PTR [esi+1120]
	mov edx, DWORD PTR [esi+1124]
	xor eax, DWORD PTR [esi+1024]
	xor edx, DWORD PTR [esi+1028]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1120], edx
	mov DWORD PTR [esi+1124], eax
	mov edx, DWORD PTR [esi+1120]
	mov eax, DWORD PTR [esi+1088]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1120]
	adc edx, DWORD PTR [esi+1124]
	add eax, DWORD PTR [esi+1088]
	adc edx, DWORD PTR [esi+1092]
	mov DWORD PTR [esi+1088], eax
	mov DWORD PTR [esi+1092], edx
	mov eax, DWORD PTR [esi+1056]
	mov edx, DWORD PTR [esi+1060]
	xor eax, DWORD PTR [esi+1088]
	xor edx, DWORD PTR [esi+1092]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1056], eax
	mov DWORD PTR [esi+1060], edx
	mov edx, DWORD PTR [esi+1064]
	mov eax, DWORD PTR [esi+1032]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1064]
	adc edx, DWORD PTR [esi+1068]
	add eax, DWORD PTR [esi+1032]
	adc edx, DWORD PTR [esi+1036]
	mov DWORD PTR [esi+1032], eax
	mov DWORD PTR [esi+1036], edx
	mov eax, DWORD PTR [esi+1128]
	mov edx, DWORD PTR [esi+1132]
	xor eax, DWORD PTR [esi+1032]
	xor edx, DWORD PTR [esi+1036]
	mov DWORD PTR [esi+1128], edx
	mov DWORD PTR [esi+1132], eax
	mov edx, DWORD PTR [esi+1128]
	mov eax, DWORD PTR [esi+1096]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1128]
	adc edx, DWORD PTR [esi+1132]
	add eax, DWORD PTR [esi+1096]
	adc edx, DWORD PTR [esi+1100]
	mov DWORD PTR [esi+1096], eax
	mov DWORD PTR [esi+1100], edx
	mov eax, DWORD PTR [esi+1064]
	mov edx, DWORD PTR [esi+1068]
	xor eax, DWORD PTR [esi+1096]
	xor edx, DWORD PTR [esi+1100]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1064], edx
	mov DWORD PTR [esi+1068], eax
	mov edx, DWORD PTR [esi+1064]
	mov eax, DWORD PTR [esi+1032]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1064]
	adc edx, DWORD PTR [esi+1068]
	add eax, DWORD PTR [esi+1032]
	adc edx, DWORD PTR [esi+1036]
	mov DWORD PTR [esi+1032], eax
	mov DWORD PTR [esi+1036], edx
	mov eax, DWORD PTR [esi+1128]
	mov edx, DWORD PTR [esi+1132]
	xor eax, DWORD PTR [esi+1032]
	xor edx, DWORD PTR [esi+1036]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1128], edx
	mov DWORD PTR [esi+1132], eax
	mov edx, DWORD PTR [esi+1128]
	mov eax, DWORD PTR [esi+1096]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1128]
	adc edx, DWORD PTR [esi+1132]
	add eax, DWORD PTR [esi+1096]
	adc edx, DWORD PTR [esi+1100]
	mov DWORD PTR [esi+1096], eax
	mov DWORD PTR [esi+1100], edx
	mov eax, DWORD PTR [esi+1064]
	mov edx, DWORD PTR [esi+1068]
	xor eax, DWORD PTR [esi+1096]
	xor edx, DWORD PTR [esi+1100]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1064], eax
	mov DWORD PTR [esi+1068], edx
	mov edx, DWORD PTR [esi+1072]
	mov eax, DWORD PTR [esi+1040]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1072]
	adc edx, DWORD PTR [esi+1076]
	add eax, DWORD PTR [esi+1040]
	adc edx, DWORD PTR [esi+1044]
	mov DWORD PTR [esi+1040], eax
	mov DWORD PTR [esi+1044], edx
	mov eax, DWORD PTR [esi+1136]
	mov edx, DWORD PTR [esi+1140]
	xor eax, DWORD PTR [esi+1040]
	xor edx, DWORD PTR [esi+1044]
	mov DWORD PTR [esi+1136], edx
	mov DWORD PTR [esi+1140], eax
	mov edx, DWORD PTR [esi+1136]
	mov eax, DWORD PTR [esi+1104]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1136]
	adc edx, DWORD PTR [esi+1140]
	add eax, DWORD PTR [esi+1104]
	adc edx, DWORD PTR [esi+1108]
	mov DWORD PTR [esi+1104], eax
	mov DWORD PTR [esi+1108], edx
	mov eax, DWORD PTR [esi+1072]
	mov edx, DWORD PTR [esi+1076]
	xor eax, DWORD PTR [esi+1104]
	xor edx, DWORD PTR [esi+1108]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1072], edx
	mov DWORD PTR [esi+1076], eax
	mov edx, DWORD PTR [esi+1072]
	mov eax, DWORD PTR [esi+1040]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1072]
	adc edx, DWORD PTR [esi+1076]
	add eax, DWORD PTR [esi+1040]
	adc edx, DWORD PTR [esi+1044]
	mov DWORD PTR [esi+1040], eax
	mov DWORD PTR [esi+1044], edx
	mov eax, DWORD PTR [esi+1136]
	mov edx, DWORD PTR [esi+1140]
	xor eax, DWORD PTR [esi+1040]
	xor edx, DWORD PTR [esi+1044]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1136], edx
	mov DWORD PTR [esi+1140], eax
	mov edx, DWORD PTR [esi+1136]
	mov eax, DWORD PTR [esi+1104]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1136]
	adc edx, DWORD PTR [esi+1140]
	add eax, DWORD PTR [esi+1104]
	adc edx, DWORD PTR [esi+1108]
	mov DWORD PTR [esi+1104], eax
	mov DWORD PTR [esi+1108], edx
	mov eax, DWORD PTR [esi+1072]
	mov edx, DWORD PTR [esi+1076]
	xor eax, DWORD PTR [esi+1104]
	xor edx, DWORD PTR [esi+1108]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1072], eax
	mov DWORD PTR [esi+1076], edx
	mov edx, DWORD PTR [esi+1080]
	mov eax, DWORD PTR [esi+1048]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1080]
	adc edx, DWORD PTR [esi+1084]
	add eax, DWORD PTR [esi+1048]
	adc edx, DWORD PTR [esi+1052]
	mov DWORD PTR [esi+1048], eax
	mov DWORD PTR [esi+1052], edx
	mov eax, DWORD PTR [esi+1144]
	mov edx, DWORD PTR [esi+1148]
	xor eax, DWORD PTR [esi+1048]
	xor edx, DWORD PTR [esi+1052]
	mov DWORD PTR [esi+1144], edx
	mov DWORD PTR [esi+1148], eax
	mov edx, DWORD PTR [esi+1144]
	mov eax, DWORD PTR [esi+1112]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1144]
	adc edx, DWORD PTR [esi+1148]
	add eax, DWORD PTR [esi+1112]
	adc edx, DWORD PTR [esi+1116]
	mov DWORD PTR [esi+1112], eax
	mov DWORD PTR [esi+1116], edx
	mov eax, DWORD PTR [esi+1080]
	mov edx, DWORD PTR [esi+1084]
	xor eax, DWORD PTR [esi+1112]
	xor edx, DWORD PTR [esi+1116]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1080], edx
	mov DWORD PTR [esi+1084], eax
	mov edx, DWORD PTR [esi+1080]
	mov eax, DWORD PTR [esi+1048]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1080]
	adc edx, DWORD PTR [esi+1084]
	add eax, DWORD PTR [esi+1048]
	adc edx, DWORD PTR [esi+1052]
	mov DWORD PTR [esi+1048], eax
	mov DWORD PTR [esi+1052], edx
	mov eax, DWORD PTR [esi+1144]
	mov edx, DWORD PTR [esi+1148]
	xor eax, DWORD PTR [esi+1048]
	xor edx, DWORD PTR [esi+1052]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1144], edx
	mov DWORD PTR [esi+1148], eax
	mov edx, DWORD PTR [esi+1144]
	mov eax, DWORD PTR [esi+1112]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1144]
	adc edx, DWORD PTR [esi+1148]
	add eax, DWORD PTR [esi+1112]
	adc edx, DWORD PTR [esi+1116]
	mov DWORD PTR [esi+1112], eax
	mov DWORD PTR [esi+1116], edx
	mov eax, DWORD PTR [esi+1080]
	mov edx, DWORD PTR [esi+1084]
	xor eax, DWORD PTR [esi+1112]
	xor edx, DWORD PTR [esi+1116]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1080], eax
	mov DWORD PTR [esi+1084], edx
	mov edx, DWORD PTR [esi+1064]
	mov eax, DWORD PTR [esi+1024]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1064]
	adc edx, DWORD PTR [esi+1068]
	add eax, DWORD PTR [esi+1024]
	adc edx, DWORD PTR [esi+1028]
	mov DWORD PTR [esi+1024], eax
	mov DWORD PTR [esi+1028], edx
	mov eax, DWORD PTR [esi+1144]
	mov edx, DWORD PTR [esi+1148]
	xor eax, DWORD PTR [esi+1024]
	xor edx, DWORD PTR [esi+1028]
	mov DWORD PTR [esi+1144], edx
	mov DWORD PTR [esi+1148], eax
	mov edx, DWORD PTR [esi+1144]
	mov eax, DWORD PTR [esi+1104]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1144]
	adc edx, DWORD PTR [esi+1148]
	add eax, DWORD PTR [esi+1104]
	adc edx, DWORD PTR [esi+1108]
	mov DWORD PTR [esi+1104], eax
	mov DWORD PTR [esi+1108], edx
	mov eax, DWORD PTR [esi+1064]
	mov edx, DWORD PTR [esi+1068]
	xor eax, DWORD PTR [esi+1104]
	xor edx, DWORD PTR [esi+1108]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1064], edx
	mov DWORD PTR [esi+1068], eax
	mov edx, DWORD PTR [esi+1064]
	mov eax, DWORD PTR [esi+1024]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1064]
	adc edx, DWORD PTR [esi+1068]
	add eax, DWORD PTR [esi+1024]
	adc edx, DWORD PTR [esi+1028]
	mov DWORD PTR [esi+1024], eax
	mov DWORD PTR [esi+1028], edx
	mov eax, DWORD PTR [esi+1144]
	mov edx, DWORD PTR [esi+1148]
	xor eax, DWORD PTR [esi+1024]
	xor edx, DWORD PTR [esi+1028]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1144], edx
	mov DWORD PTR [esi+1148], eax
	mov edx, DWORD PTR [esi+1144]
	mov eax, DWORD PTR [esi+1104]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1144]
	adc edx, DWORD PTR [esi+1148]
	add eax, DWORD PTR [esi+1104]
	adc edx, DWORD PTR [esi+1108]
	mov DWORD PTR [esi+1104], eax
	mov DWORD PTR [esi+1108], edx
	mov eax, DWORD PTR [esi+1064]
	mov edx, DWORD PTR [esi+1068]
	xor eax, DWORD PTR [esi+1104]
	xor edx, DWORD PTR [esi+1108]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1064], eax
	mov DWORD PTR [esi+1068], edx
	mov edx, DWORD PTR [esi+1072]
	mov eax, DWORD PTR [esi+1032]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1072]
	adc edx, DWORD PTR [esi+1076]
	add eax, DWORD PTR [esi+1032]
	adc edx, DWORD PTR [esi+1036]
	mov DWORD PTR [esi+1032], eax
	mov DWORD PTR [esi+1036], edx
	mov eax, DWORD PTR [esi+1120]
	mov edx, DWORD PTR [esi+1124]
	xor eax, DWORD PTR [esi+1032]
	xor edx, DWORD PTR [esi+1036]
	mov DWORD PTR [esi+1120], edx
	mov DWORD PTR [esi+1124], eax
	mov edx, DWORD PTR [esi+1120]
	mov eax, DWORD PTR [esi+1112]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1120]
	adc edx, DWORD PTR [esi+1124]
	add eax, DWORD PTR [esi+1112]
	adc edx, DWORD PTR [esi+1116]
	mov DWORD PTR [esi+1112], eax
	mov DWORD PTR [esi+1116], edx
	mov eax, DWORD PTR [esi+1072]
	mov edx, DWORD PTR [esi+1076]
	xor eax, DWORD PTR [esi+1112]
	xor edx, DWORD PTR [esi+1116]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1072], edx
	mov DWORD PTR [esi+1076], eax
	mov edx, DWORD PTR [esi+1072]
	mov eax, DWORD PTR [esi+1032]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1072]
	adc edx, DWORD PTR [esi+1076]
	add eax, DWORD PTR [esi+1032]
	adc edx, DWORD PTR [esi+1036]
	mov DWORD PTR [esi+1032], eax
	mov DWORD PTR [esi+1036], edx
	mov eax, DWORD PTR [esi+1120]
	mov edx, DWORD PTR [esi+1124]
	xor eax, DWORD PTR [esi+1032]
	xor edx, DWORD PTR [esi+1036]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1120], edx
	mov DWORD PTR [esi+1124], eax
	mov edx, DWORD PTR [esi+1120]
	mov eax, DWORD PTR [esi+1112]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1120]
	adc edx, DWORD PTR [esi+1124]
	add eax, DWORD PTR [esi+1112]
	adc edx, DWORD PTR [esi+1116]
	mov DWORD PTR [esi+1112], eax
	mov DWORD PTR [esi+1116], edx
	mov eax, DWORD PTR [esi+1072]
	mov edx, DWORD PTR [esi+1076]
	xor eax, DWORD PTR [esi+1112]
	xor edx, DWORD PTR [esi+1116]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1072], eax
	mov DWORD PTR [esi+1076], edx
	mov edx, DWORD PTR [esi+1080]
	mov eax, DWORD PTR [esi+1040]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1080]
	adc edx, DWORD PTR [esi+1084]
	add eax, DWORD PTR [esi+1040]
	adc edx, DWORD PTR [esi+1044]
	mov DWORD PTR [esi+1040], eax
	mov DWORD PTR [esi+1044], edx
	mov eax, DWORD PTR [esi+1128]
	mov edx, DWORD PTR [esi+1132]
	xor eax, DWORD PTR [esi+1040]
	xor edx, DWORD PTR [esi+1044]
	mov DWORD PTR [esi+1128], edx
	mov DWORD PTR [esi+1132], eax
	mov edx, DWORD PTR [esi+1128]
	mov eax, DWORD PTR [esi+1088]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1128]
	adc edx, DWORD PTR [esi+1132]
	add eax, DWORD PTR [esi+1088]
	adc edx, DWORD PTR [esi+1092]
	mov DWORD PTR [esi+1088], eax
	mov DWORD PTR [esi+1092], edx
	mov eax, DWORD PTR [esi+1080]
	mov edx, DWORD PTR [esi+1084]
	xor eax, DWORD PTR [esi+1088]
	xor edx, DWORD PTR [esi+1092]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1080], edx
	mov DWORD PTR [esi+1084], eax
	mov edx, DWORD PTR [esi+1080]
	mov eax, DWORD PTR [esi+1040]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1080]
	adc edx, DWORD PTR [esi+1084]
	add eax, DWORD PTR [esi+1040]
	adc edx, DWORD PTR [esi+1044]
	mov DWORD PTR [esi+1040], eax
	mov DWORD PTR [esi+1044], edx
	mov eax, DWORD PTR [esi+1128]
	mov edx, DWORD PTR [esi+1132]
	xor eax, DWORD PTR [esi+1040]
	xor edx, DWORD PTR [esi+1044]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1128], edx
	mov DWORD PTR [esi+1132], eax
	mov edx, DWORD PTR [esi+1128]
	mov eax, DWORD PTR [esi+1088]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1128]
	adc edx, DWORD PTR [esi+1132]
	add eax, DWORD PTR [esi+1088]
	adc edx, DWORD PTR [esi+1092]
	mov DWORD PTR [esi+1088], eax
	mov DWORD PTR [esi+1092], edx
	mov eax, DWORD PTR [esi+1080]
	mov edx, DWORD PTR [esi+1084]
	xor eax, DWORD PTR [esi+1088]
	xor edx, DWORD PTR [esi+1092]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1080], eax
	mov DWORD PTR [esi+1084], edx
	mov edx, DWORD PTR [esi+1056]
	mov eax, DWORD PTR [esi+1048]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1056]
	adc edx, DWORD PTR [esi+1060]
	add eax, DWORD PTR [esi+1048]
	adc edx, DWORD PTR [esi+1052]
	mov DWORD PTR [esi+1048], eax
	mov DWORD PTR [esi+1052], edx
	mov eax, DWORD PTR [esi+1136]
	mov edx, DWORD PTR [esi+1140]
	xor eax, DWORD PTR [esi+1048]
	xor edx, DWORD PTR [esi+1052]
	mov DWORD PTR [esi+1136], edx
	mov DWORD PTR [esi+1140], eax
	mov edx, DWORD PTR [esi+1136]
	mov eax, DWORD PTR [esi+1096]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1136]
	adc edx, DWORD PTR [esi+1140]
	add eax, DWORD PTR [esi+1096]
	adc edx, DWORD PTR [esi+1100]
	mov DWORD PTR [esi+1096], eax
	mov DWORD PTR [esi+1100], edx
	mov eax, DWORD PTR [esi+1056]
	mov edx, DWORD PTR [esi+1060]
	xor eax, DWORD PTR [esi+1096]
	xor edx, DWORD PTR [esi+1100]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1056], edx
	mov DWORD PTR [esi+1060], eax
	mov edx, DWORD PTR [esi+1056]
	mov eax, DWORD PTR [esi+1048]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1056]
	adc edx, DWORD PTR [esi+1060]
	add eax, DWORD PTR [esi+1048]
	adc edx, DWORD PTR [esi+1052]
	mov DWORD PTR [esi+1048], eax
	mov DWORD PTR [esi+1052], edx
	mov eax, DWORD PTR [esi+1136]
	mov edx, DWORD PTR [esi+1140]
	xor eax, DWORD PTR [esi+1048]
	xor edx, DWORD PTR [esi+1052]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1136], edx
	mov DWORD PTR [esi+1140], eax
	mov edx, DWORD PTR [esi+1136]
	mov eax, DWORD PTR [esi+1096]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1136]
	adc edx, DWORD PTR [esi+1140]
	add eax, DWORD PTR [esi+1096]
	adc edx, DWORD PTR [esi+1100]
	mov DWORD PTR [esi+1096], eax
	mov DWORD PTR [esi+1100], edx
	mov eax, DWORD PTR [esi+1056]
	mov edx, DWORD PTR [esi+1060]
	xor eax, DWORD PTR [esi+1096]
	xor edx, DWORD PTR [esi+1100]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1056], eax
	mov DWORD PTR [esi+1060], edx
	mov edx, DWORD PTR [esi+1184]
	mov eax, DWORD PTR [esi+1152]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1184]
	adc edx, DWORD PTR [esi+1188]
	add eax, DWORD PTR [esi+1152]
	adc edx, DWORD PTR [esi+1156]
	mov DWORD PTR [esi+1152], eax
	mov DWORD PTR [esi+1156], edx
	mov eax, DWORD PTR [esi+1248]
	mov edx, DWORD PTR [esi+1252]
	xor eax, DWORD PTR [esi+1152]
	xor edx, DWORD PTR [esi+1156]
	mov DWORD PTR [esi+1248], edx
	mov DWORD PTR [esi+1252], eax
	mov edx, DWORD PTR [esi+1248]
	mov eax, DWORD PTR [esi+1216]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1248]
	adc edx, DWORD PTR [esi+1252]
	add eax, DWORD PTR [esi+1216]
	adc edx, DWORD PTR [esi+1220]
	mov DWORD PTR [esi+1216], eax
	mov DWORD PTR [esi+1220], edx
	mov eax, DWORD PTR [esi+1184]
	mov edx, DWORD PTR [esi+1188]
	xor eax, DWORD PTR [esi+1216]
	xor edx, DWORD PTR [esi+1220]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1184], edx
	mov DWORD PTR [esi+1188], eax
	mov edx, DWORD PTR [esi+1184]
	mov eax, DWORD PTR [esi+1152]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1184]
	adc edx, DWORD PTR [esi+1188]
	add eax, DWORD PTR [esi+1152]
	adc edx, DWORD PTR [esi+1156]
	mov DWORD PTR [esi+1152], eax
	mov DWORD PTR [esi+1156], edx
	mov eax, DWORD PTR [esi+1248]
	mov edx, DWORD PTR [esi+1252]
	xor eax, DWORD PTR [esi+1152]
	xor edx, DWORD PTR [esi+1156]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1248], edx
	mov DWORD PTR [esi+1252], eax
	mov edx, DWORD PTR [esi+1248]
	mov eax, DWORD PTR [esi+1216]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1248]
	adc edx, DWORD PTR [esi+1252]
	add eax, DWORD PTR [esi+1216]
	adc edx, DWORD PTR [esi+1220]
	mov DWORD PTR [esi+1216], eax
	mov DWORD PTR [esi+1220], edx
	mov eax, DWORD PTR [esi+1184]
	mov edx, DWORD PTR [esi+1188]
	xor eax, DWORD PTR [esi+1216]
	xor edx, DWORD PTR [esi+1220]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1184], eax
	mov DWORD PTR [esi+1188], edx
	mov edx, DWORD PTR [esi+1192]
	mov eax, DWORD PTR [esi+1160]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1192]
	adc edx, DWORD PTR [esi+1196]
	add eax, DWORD PTR [esi+1160]
	adc edx, DWORD PTR [esi+1164]
	mov DWORD PTR [esi+1160], eax
	mov DWORD PTR [esi+1164], edx
	mov eax, DWORD PTR [esi+1256]
	mov edx, DWORD PTR [esi+1260]
	xor eax, DWORD PTR [esi+1160]
	xor edx, DWORD PTR [esi+1164]
	mov DWORD PTR [esi+1256], edx
	mov DWORD PTR [esi+1260], eax
	mov edx, DWORD PTR [esi+1256]
	mov eax, DWORD PTR [esi+1224]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1256]
	adc edx, DWORD PTR [esi+1260]
	add eax, DWORD PTR [esi+1224]
	adc edx, DWORD PTR [esi+1228]
	mov DWORD PTR [esi+1224], eax
	mov DWORD PTR [esi+1228], edx
	mov eax, DWORD PTR [esi+1192]
	mov edx, DWORD PTR [esi+1196]
	xor eax, DWORD PTR [esi+1224]
	xor edx, DWORD PTR [esi+1228]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1192], edx
	mov DWORD PTR [esi+1196], eax
	mov edx, DWORD PTR [esi+1192]
	mov eax, DWORD PTR [esi+1160]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1192]
	adc edx, DWORD PTR [esi+1196]
	add eax, DWORD PTR [esi+1160]
	adc edx, DWORD PTR [esi+1164]
	mov DWORD PTR [esi+1160], eax
	mov DWORD PTR [esi+1164], edx
	mov eax, DWORD PTR [esi+1256]
	mov edx, DWORD PTR [esi+1260]
	xor eax, DWORD PTR [esi+1160]
	xor edx, DWORD PTR [esi+1164]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1256], edx
	mov DWORD PTR [esi+1260], eax
	mov edx, DWORD PTR [esi+1256]
	mov eax, DWORD PTR [esi+1224]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1256]
	adc edx, DWORD PTR [esi+1260]
	add eax, DWORD PTR [esi+1224]
	adc edx, DWORD PTR [esi+1228]
	mov DWORD PTR [esi+1224], eax
	mov DWORD PTR [esi+1228], edx
	mov eax, DWORD PTR [esi+1192]
	mov edx, DWORD PTR [esi+1196]
	xor eax, DWORD PTR [esi+1224]
	xor edx, DWORD PTR [esi+1228]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1192], eax
	mov DWORD PTR [esi+1196], edx
	mov edx, DWORD PTR [esi+1200]
	mov eax, DWORD PTR [esi+1168]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1200]
	adc edx, DWORD PTR [esi+1204]
	add eax, DWORD PTR [esi+1168]
	adc edx, DWORD PTR [esi+1172]
	mov DWORD PTR [esi+1168], eax
	mov DWORD PTR [esi+1172], edx
	mov eax, DWORD PTR [esi+1264]
	mov edx, DWORD PTR [esi+1268]
	xor eax, DWORD PTR [esi+1168]
	xor edx, DWORD PTR [esi+1172]
	mov DWORD PTR [esi+1264], edx
	mov DWORD PTR [esi+1268], eax
	mov edx, DWORD PTR [esi+1264]
	mov eax, DWORD PTR [esi+1232]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1264]
	adc edx, DWORD PTR [esi+1268]
	add eax, DWORD PTR [esi+1232]
	adc edx, DWORD PTR [esi+1236]
	mov DWORD PTR [esi+1232], eax
	mov DWORD PTR [esi+1236], edx
	mov eax, DWORD PTR [esi+1200]
	mov edx, DWORD PTR [esi+1204]
	xor eax, DWORD PTR [esi+1232]
	xor edx, DWORD PTR [esi+1236]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1200], edx
	mov DWORD PTR [esi+1204], eax
	mov edx, DWORD PTR [esi+1200]
	mov eax, DWORD PTR [esi+1168]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1200]
	adc edx, DWORD PTR [esi+1204]
	add eax, DWORD PTR [esi+1168]
	adc edx, DWORD PTR [esi+1172]
	mov DWORD PTR [esi+1168], eax
	mov DWORD PTR [esi+1172], edx
	mov eax, DWORD PTR [esi+1264]
	mov edx, DWORD PTR [esi+1268]
	xor eax, DWORD PTR [esi+1168]
	xor edx, DWORD PTR [esi+1172]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1264], edx
	mov DWORD PTR [esi+1268], eax
	mov edx, DWORD PTR [esi+1264]
	mov eax, DWORD PTR [esi+1232]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1264]
	adc edx, DWORD PTR [esi+1268]
	add eax, DWORD PTR [esi+1232]
	adc edx, DWORD PTR [esi+1236]
	mov DWORD PTR [esi+1232], eax
	mov DWORD PTR [esi+1236], edx
	mov eax, DWORD PTR [esi+1200]
	mov edx, DWORD PTR [esi+1204]
	xor eax, DWORD PTR [esi+1232]
	xor edx, DWORD PTR [esi+1236]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1200], eax
	mov DWORD PTR [esi+1204], edx
	mov edx, DWORD PTR [esi+1208]
	mov eax, DWORD PTR [esi+1176]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1208]
	adc edx, DWORD PTR [esi+1212]
	add eax, DWORD PTR [esi+1176]
	adc edx, DWORD PTR [esi+1180]
	mov DWORD PTR [esi+1176], eax
	mov DWORD PTR [esi+1180], edx
	mov eax, DWORD PTR [esi+1272]
	mov edx, DWORD PTR [esi+1276]
	xor eax, DWORD PTR [esi+1176]
	xor edx, DWORD PTR [esi+1180]
	mov DWORD PTR [esi+1272], edx
	mov DWORD PTR [esi+1276], eax
	mov edx, DWORD PTR [esi+1272]
	mov eax, DWORD PTR [esi+1240]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1272]
	adc edx, DWORD PTR [esi+1276]
	add eax, DWORD PTR [esi+1240]
	adc edx, DWORD PTR [esi+1244]
	mov DWORD PTR [esi+1240], eax
	mov DWORD PTR [esi+1244], edx
	mov eax, DWORD PTR [esi+1208]
	mov edx, DWORD PTR [esi+1212]
	xor eax, DWORD PTR [esi+1240]
	xor edx, DWORD PTR [esi+1244]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1208], edx
	mov DWORD PTR [esi+1212], eax
	mov edx, DWORD PTR [esi+1208]
	mov eax, DWORD PTR [esi+1176]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1208]
	adc edx, DWORD PTR [esi+1212]
	add eax, DWORD PTR [esi+1176]
	adc edx, DWORD PTR [esi+1180]
	mov DWORD PTR [esi+1176], eax
	mov DWORD PTR [esi+1180], edx
	mov eax, DWORD PTR [esi+1272]
	mov edx, DWORD PTR [esi+1276]
	xor eax, DWORD PTR [esi+1176]
	xor edx, DWORD PTR [esi+1180]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1272], edx
	mov DWORD PTR [esi+1276], eax
	mov edx, DWORD PTR [esi+1272]
	mov eax, DWORD PTR [esi+1240]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1272]
	adc edx, DWORD PTR [esi+1276]
	add eax, DWORD PTR [esi+1240]
	adc edx, DWORD PTR [esi+1244]
	mov DWORD PTR [esi+1240], eax
	mov DWORD PTR [esi+1244], edx
	mov eax, DWORD PTR [esi+1208]
	mov edx, DWORD PTR [esi+1212]
	xor eax, DWORD PTR [esi+1240]
	xor edx, DWORD PTR [esi+1244]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1208], eax
	mov DWORD PTR [esi+1212], edx
	mov edx, DWORD PTR [esi+1192]
	mov eax, DWORD PTR [esi+1152]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1192]
	adc edx, DWORD PTR [esi+1196]
	add eax, DWORD PTR [esi+1152]
	adc edx, DWORD PTR [esi+1156]
	mov DWORD PTR [esi+1152], eax
	mov DWORD PTR [esi+1156], edx
	mov eax, DWORD PTR [esi+1272]
	mov edx, DWORD PTR [esi+1276]
	xor eax, DWORD PTR [esi+1152]
	xor edx, DWORD PTR [esi+1156]
	mov DWORD PTR [esi+1272], edx
	mov DWORD PTR [esi+1276], eax
	mov edx, DWORD PTR [esi+1272]
	mov eax, DWORD PTR [esi+1232]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1272]
	adc edx, DWORD PTR [esi+1276]
	add eax, DWORD PTR [esi+1232]
	adc edx, DWORD PTR [esi+1236]
	mov DWORD PTR [esi+1232], eax
	mov DWORD PTR [esi+1236], edx
	mov eax, DWORD PTR [esi+1192]
	mov edx, DWORD PTR [esi+1196]
	xor eax, DWORD PTR [esi+1232]
	xor edx, DWORD PTR [esi+1236]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1192], edx
	mov DWORD PTR [esi+1196], eax
	mov edx, DWORD PTR [esi+1192]
	mov eax, DWORD PTR [esi+1152]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1192]
	adc edx, DWORD PTR [esi+1196]
	add eax, DWORD PTR [esi+1152]
	adc edx, DWORD PTR [esi+1156]
	mov DWORD PTR [esi+1152], eax
	mov DWORD PTR [esi+1156], edx
	mov eax, DWORD PTR [esi+1272]
	mov edx, DWORD PTR [esi+1276]
	xor eax, DWORD PTR [esi+1152]
	xor edx, DWORD PTR [esi+1156]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1272], edx
	mov DWORD PTR [esi+1276], eax
	mov edx, DWORD PTR [esi+1272]
	mov eax, DWORD PTR [esi+1232]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1272]
	adc edx, DWORD PTR [esi+1276]
	add eax, DWORD PTR [esi+1232]
	adc edx, DWORD PTR [esi+1236]
	mov DWORD PTR [esi+1232], eax
	mov DWORD PTR [esi+1236], edx
	mov eax, DWORD PTR [esi+1192]
	mov edx, DWORD PTR [esi+1196]
	xor eax, DWORD PTR [esi+1232]
	xor edx, DWORD PTR [esi+1236]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1192], eax
	mov DWORD PTR [esi+1196], edx
	mov edx, DWORD PTR [esi+1200]
	mov eax, DWORD PTR [esi+1160]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1200]
	adc edx, DWORD PTR [esi+1204]
	add eax, DWORD PTR [esi+1160]
	adc edx, DWORD PTR [esi+1164]
	mov DWORD PTR [esi+1160], eax
	mov DWORD PTR [esi+1164], edx
	mov eax, DWORD PTR [esi+1248]
	mov edx, DWORD PTR [esi+1252]
	xor eax, DWORD PTR [esi+1160]
	xor edx, DWORD PTR [esi+1164]
	mov DWORD PTR [esi+1248], edx
	mov DWORD PTR [esi+1252], eax
	mov edx, DWORD PTR [esi+1248]
	mov eax, DWORD PTR [esi+1240]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1248]
	adc edx, DWORD PTR [esi+1252]
	add eax, DWORD PTR [esi+1240]
	adc edx, DWORD PTR [esi+1244]
	mov DWORD PTR [esi+1240], eax
	mov DWORD PTR [esi+1244], edx
	mov eax, DWORD PTR [esi+1200]
	mov edx, DWORD PTR [esi+1204]
	xor eax, DWORD PTR [esi+1240]
	xor edx, DWORD PTR [esi+1244]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1200], edx
	mov DWORD PTR [esi+1204], eax
	mov edx, DWORD PTR [esi+1200]
	mov eax, DWORD PTR [esi+1160]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1200]
	adc edx, DWORD PTR [esi+1204]
	add eax, DWORD PTR [esi+1160]
	adc edx, DWORD PTR [esi+1164]
	mov DWORD PTR [esi+1160], eax
	mov DWORD PTR [esi+1164], edx
	mov eax, DWORD PTR [esi+1248]
	mov edx, DWORD PTR [esi+1252]
	xor eax, DWORD PTR [esi+1160]
	xor edx, DWORD PTR [esi+1164]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1248], edx
	mov DWORD PTR [esi+1252], eax
	mov edx, DWORD PTR [esi+1248]
	mov eax, DWORD PTR [esi+1240]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1248]
	adc edx, DWORD PTR [esi+1252]
	add eax, DWORD PTR [esi+1240]
	adc edx, DWORD PTR [esi+1244]
	mov DWORD PTR [esi+1240], eax
	mov DWORD PTR [esi+1244], edx
	mov eax, DWORD PTR [esi+1200]
	mov edx, DWORD PTR [esi+1204]
	xor eax, DWORD PTR [esi+1240]
	xor edx, DWORD PTR [esi+1244]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1200], eax
	mov DWORD PTR [esi+1204], edx
	mov edx, DWORD PTR [esi+1208]
	mov eax, DWORD PTR [esi+1168]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1208]
	adc edx, DWORD PTR [esi+1212]
	add eax, DWORD PTR [esi+1168]
	adc edx, DWORD PTR [esi+1172]
	mov DWORD PTR [esi+1168], eax
	mov DWORD PTR [esi+1172], edx
	mov eax, DWORD PTR [esi+1256]
	mov edx, DWORD PTR [esi+1260]
	xor eax, DWORD PTR [esi+1168]
	xor edx, DWORD PTR [esi+1172]
	mov DWORD PTR [esi+1256], edx
	mov DWORD PTR [esi+1260], eax
	mov edx, DWORD PTR [esi+1256]
	mov eax, DWORD PTR [esi+1216]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1256]
	adc edx, DWORD PTR [esi+1260]
	add eax, DWORD PTR [esi+1216]
	adc edx, DWORD PTR [esi+1220]
	mov DWORD PTR [esi+1216], eax
	mov DWORD PTR [esi+1220], edx
	mov eax, DWORD PTR [esi+1208]
	mov edx, DWORD PTR [esi+1212]
	xor eax, DWORD PTR [esi+1216]
	xor edx, DWORD PTR [esi+1220]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1208], edx
	mov DWORD PTR [esi+1212], eax
	mov edx, DWORD PTR [esi+1208]
	mov eax, DWORD PTR [esi+1168]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1208]
	adc edx, DWORD PTR [esi+1212]
	add eax, DWORD PTR [esi+1168]
	adc edx, DWORD PTR [esi+1172]
	mov DWORD PTR [esi+1168], eax
	mov DWORD PTR [esi+1172], edx
	mov eax, DWORD PTR [esi+1256]
	mov edx, DWORD PTR [esi+1260]
	xor eax, DWORD PTR [esi+1168]
	xor edx, DWORD PTR [esi+1172]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1256], edx
	mov DWORD PTR [esi+1260], eax
	mov edx, DWORD PTR [esi+1256]
	mov eax, DWORD PTR [esi+1216]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1256]
	adc edx, DWORD PTR [esi+1260]
	add eax, DWORD PTR [esi+1216]
	adc edx, DWORD PTR [esi+1220]
	mov DWORD PTR [esi+1216], eax
	mov DWORD PTR [esi+1220], edx
	mov eax, DWORD PTR [esi+1208]
	mov edx, DWORD PTR [esi+1212]
	xor eax, DWORD PTR [esi+1216]
	xor edx, DWORD PTR [esi+1220]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1208], eax
	mov DWORD PTR [esi+1212], edx
	mov edx, DWORD PTR [esi+1184]
	mov eax, DWORD PTR [esi+1176]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1184]
	adc edx, DWORD PTR [esi+1188]
	add eax, DWORD PTR [esi+1176]
	adc edx, DWORD PTR [esi+1180]
	mov DWORD PTR [esi+1176], eax
	mov DWORD PTR [esi+1180], edx
	mov eax, DWORD PTR [esi+1264]
	mov edx, DWORD PTR [esi+1268]
	xor eax, DWORD PTR [esi+1176]
	xor edx, DWORD PTR [esi+1180]
	mov DWORD PTR [esi+1264], edx
	mov DWORD PTR [esi+1268], eax
	mov edx, DWORD PTR [esi+1264]
	mov eax, DWORD PTR [esi+1224]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1264]
	adc edx, DWORD PTR [esi+1268]
	add eax, DWORD PTR [esi+1224]
	adc edx, DWORD PTR [esi+1228]
	mov DWORD PTR [esi+1224], eax
	mov DWORD PTR [esi+1228], edx
	mov eax, DWORD PTR [esi+1184]
	mov edx, DWORD PTR [esi+1188]
	xor eax, DWORD PTR [esi+1224]
	xor edx, DWORD PTR [esi+1228]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1184], edx
	mov DWORD PTR [esi+1188], eax
	mov edx, DWORD PTR [esi+1184]
	mov eax, DWORD PTR [esi+1176]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1184]
	adc edx, DWORD PTR [esi+1188]
	add eax, DWORD PTR [esi+1176]
	adc edx, DWORD PTR [esi+1180]
	mov DWORD PTR [esi+1176], eax
	mov DWORD PTR [esi+1180], edx
	mov eax, DWORD PTR [esi+1264]
	mov edx, DWORD PTR [esi+1268]
	xor eax, DWORD PTR [esi+1176]
	xor edx, DWORD PTR [esi+1180]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1264], edx
	mov DWORD PTR [esi+1268], eax
	mov edx, DWORD PTR [esi+1264]
	mov eax, DWORD PTR [esi+1224]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1264]
	adc edx, DWORD PTR [esi+1268]
	add eax, DWORD PTR [esi+1224]
	adc edx, DWORD PTR [esi+1228]
	mov DWORD PTR [esi+1224], eax
	mov DWORD PTR [esi+1228], edx
	mov eax, DWORD PTR [esi+1184]
	mov edx, DWORD PTR [esi+1188]
	xor eax, DWORD PTR [esi+1224]
	xor edx, DWORD PTR [esi+1228]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1184], eax
	mov DWORD PTR [esi+1188], edx
	mov edx, DWORD PTR [esi+1312]
	mov eax, DWORD PTR [esi+1280]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1312]
	adc edx, DWORD PTR [esi+1316]
	add eax, DWORD PTR [esi+1280]
	adc edx, DWORD PTR [esi+1284]
	mov DWORD PTR [esi+1280], eax
	mov DWORD PTR [esi+1284], edx
	mov eax, DWORD PTR [esi+1376]
	mov edx, DWORD PTR [esi+1380]
	xor eax, DWORD PTR [esi+1280]
	xor edx, DWORD PTR [esi+1284]
	mov DWORD PTR [esi+1376], edx
	mov DWORD PTR [esi+1380], eax
	mov edx, DWORD PTR [esi+1376]
	mov eax, DWORD PTR [esi+1344]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1376]
	adc edx, DWORD PTR [esi+1380]
	add eax, DWORD PTR [esi+1344]
	adc edx, DWORD PTR [esi+1348]
	mov DWORD PTR [esi+1344], eax
	mov DWORD PTR [esi+1348], edx
	mov eax, DWORD PTR [esi+1312]
	mov edx, DWORD PTR [esi+1316]
	xor eax, DWORD PTR [esi+1344]
	xor edx, DWORD PTR [esi+1348]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1312], edx
	mov DWORD PTR [esi+1316], eax
	mov edx, DWORD PTR [esi+1312]
	mov eax, DWORD PTR [esi+1280]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1312]
	adc edx, DWORD PTR [esi+1316]
	add eax, DWORD PTR [esi+1280]
	adc edx, DWORD PTR [esi+1284]
	mov DWORD PTR [esi+1280], eax
	mov DWORD PTR [esi+1284], edx
	mov eax, DWORD PTR [esi+1376]
	mov edx, DWORD PTR [esi+1380]
	xor eax, DWORD PTR [esi+1280]
	xor edx, DWORD PTR [esi+1284]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1376], edx
	mov DWORD PTR [esi+1380], eax
	mov edx, DWORD PTR [esi+1376]
	mov eax, DWORD PTR [esi+1344]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1376]
	adc edx, DWORD PTR [esi+1380]
	add eax, DWORD PTR [esi+1344]
	adc edx, DWORD PTR [esi+1348]
	mov DWORD PTR [esi+1344], eax
	mov DWORD PTR [esi+1348], edx
	mov eax, DWORD PTR [esi+1312]
	mov edx, DWORD PTR [esi+1316]
	xor eax, DWORD PTR [esi+1344]
	xor edx, DWORD PTR [esi+1348]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1312], eax
	mov DWORD PTR [esi+1316], edx
	mov edx, DWORD PTR [esi+1320]
	mov eax, DWORD PTR [esi+1288]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1320]
	adc edx, DWORD PTR [esi+1324]
	add eax, DWORD PTR [esi+1288]
	adc edx, DWORD PTR [esi+1292]
	mov DWORD PTR [esi+1288], eax
	mov DWORD PTR [esi+1292], edx
	mov eax, DWORD PTR [esi+1384]
	mov edx, DWORD PTR [esi+1388]
	xor eax, DWORD PTR [esi+1288]
	xor edx, DWORD PTR [esi+1292]
	mov DWORD PTR [esi+1384], edx
	mov DWORD PTR [esi+1388], eax
	mov edx, DWORD PTR [esi+1384]
	mov eax, DWORD PTR [esi+1352]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1384]
	adc edx, DWORD PTR [esi+1388]
	add eax, DWORD PTR [esi+1352]
	adc edx, DWORD PTR [esi+1356]
	mov DWORD PTR [esi+1352], eax
	mov DWORD PTR [esi+1356], edx
	mov eax, DWORD PTR [esi+1320]
	mov edx, DWORD PTR [esi+1324]
	xor eax, DWORD PTR [esi+1352]
	xor edx, DWORD PTR [esi+1356]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1320], edx
	mov DWORD PTR [esi+1324], eax
	mov edx, DWORD PTR [esi+1320]
	mov eax, DWORD PTR [esi+1288]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1320]
	adc edx, DWORD PTR [esi+1324]
	add eax, DWORD PTR [esi+1288]
	adc edx, DWORD PTR [esi+1292]
	mov DWORD PTR [esi+1288], eax
	mov DWORD PTR [esi+1292], edx
	mov eax, DWORD PTR [esi+1384]
	mov edx, DWORD PTR [esi+1388]
	xor eax, DWORD PTR [esi+1288]
	xor edx, DWORD PTR [esi+1292]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1384], edx
	mov DWORD PTR [esi+1388], eax
	mov edx, DWORD PTR [esi+1384]
	mov eax, DWORD PTR [esi+1352]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1384]
	adc edx, DWORD PTR [esi+1388]
	add eax, DWORD PTR [esi+1352]
	adc edx, DWORD PTR [esi+1356]
	mov DWORD PTR [esi+1352], eax
	mov DWORD PTR [esi+1356], edx
	mov eax, DWORD PTR [esi+1320]
	mov edx, DWORD PTR [esi+1324]
	xor eax, DWORD PTR [esi+1352]
	xor edx, DWORD PTR [esi+1356]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1320], eax
	mov DWORD PTR [esi+1324], edx
	mov edx, DWORD PTR [esi+1328]
	mov eax, DWORD PTR [esi+1296]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1328]
	adc edx, DWORD PTR [esi+1332]
	add eax, DWORD PTR [esi+1296]
	adc edx, DWORD PTR [esi+1300]
	mov DWORD PTR [esi+1296], eax
	mov DWORD PTR [esi+1300], edx
	mov eax, DWORD PTR [esi+1392]
	mov edx, DWORD PTR [esi+1396]
	xor eax, DWORD PTR [esi+1296]
	xor edx, DWORD PTR [esi+1300]
	mov DWORD PTR [esi+1392], edx
	mov DWORD PTR [esi+1396], eax
	mov edx, DWORD PTR [esi+1392]
	mov eax, DWORD PTR [esi+1360]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1392]
	adc edx, DWORD PTR [esi+1396]
	add eax, DWORD PTR [esi+1360]
	adc edx, DWORD PTR [esi+1364]
	mov DWORD PTR [esi+1360], eax
	mov DWORD PTR [esi+1364], edx
	mov eax, DWORD PTR [esi+1328]
	mov edx, DWORD PTR [esi+1332]
	xor eax, DWORD PTR [esi+1360]
	xor edx, DWORD PTR [esi+1364]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1328], edx
	mov DWORD PTR [esi+1332], eax
	mov edx, DWORD PTR [esi+1328]
	mov eax, DWORD PTR [esi+1296]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1328]
	adc edx, DWORD PTR [esi+1332]
	add eax, DWORD PTR [esi+1296]
	adc edx, DWORD PTR [esi+1300]
	mov DWORD PTR [esi+1296], eax
	mov DWORD PTR [esi+1300], edx
	mov eax, DWORD PTR [esi+1392]
	mov edx, DWORD PTR [esi+1396]
	xor eax, DWORD PTR [esi+1296]
	xor edx, DWORD PTR [esi+1300]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1392], edx
	mov DWORD PTR [esi+1396], eax
	mov edx, DWORD PTR [esi+1392]
	mov eax, DWORD PTR [esi+1360]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1392]
	adc edx, DWORD PTR [esi+1396]
	add eax, DWORD PTR [esi+1360]
	adc edx, DWORD PTR [esi+1364]
	mov DWORD PTR [esi+1360], eax
	mov DWORD PTR [esi+1364], edx
	mov eax, DWORD PTR [esi+1328]
	mov edx, DWORD PTR [esi+1332]
	xor eax, DWORD PTR [esi+1360]
	xor edx, DWORD PTR [esi+1364]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1328], eax
	mov DWORD PTR [esi+1332], edx
	mov edx, DWORD PTR [esi+1336]
	mov eax, DWORD PTR [esi+1304]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1336]
	adc edx, DWORD PTR [esi+1340]
	add eax, DWORD PTR [esi+1304]
	adc edx, DWORD PTR [esi+1308]
	mov DWORD PTR [esi+1304], eax
	mov DWORD PTR [esi+1308], edx
	mov eax, DWORD PTR [esi+1400]
	mov edx, DWORD PTR [esi+1404]
	xor eax, DWORD PTR [esi+1304]
	xor edx, DWORD PTR [esi+1308]
	mov DWORD PTR [esi+1400], edx
	mov DWORD PTR [esi+1404], eax
	mov edx, DWORD PTR [esi+1400]
	mov eax, DWORD PTR [esi+1368]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1400]
	adc edx, DWORD PTR [esi+1404]
	add eax, DWORD PTR [esi+1368]
	adc edx, DWORD PTR [esi+1372]
	mov DWORD PTR [esi+1368], eax
	mov DWORD PTR [esi+1372], edx
	mov eax, DWORD PTR [esi+1336]
	mov edx, DWORD PTR [esi+1340]
	xor eax, DWORD PTR [esi+1368]
	xor edx, DWORD PTR [esi+1372]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1336], edx
	mov DWORD PTR [esi+1340], eax
	mov edx, DWORD PTR [esi+1336]
	mov eax, DWORD PTR [esi+1304]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1336]
	adc edx, DWORD PTR [esi+1340]
	add eax, DWORD PTR [esi+1304]
	adc edx, DWORD PTR [esi+1308]
	mov DWORD PTR [esi+1304], eax
	mov DWORD PTR [esi+1308], edx
	mov eax, DWORD PTR [esi+1400]
	mov edx, DWORD PTR [esi+1404]
	xor eax, DWORD PTR [esi+1304]
	xor edx, DWORD PTR [esi+1308]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1400], edx
	mov DWORD PTR [esi+1404], eax
	mov edx, DWORD PTR [esi+1400]
	mov eax, DWORD PTR [esi+1368]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1400]
	adc edx, DWORD PTR [esi+1404]
	add eax, DWORD PTR [esi+1368]
	adc edx, DWORD PTR [esi+1372]
	mov DWORD PTR [esi+1368], eax
	mov DWORD PTR [esi+1372], edx
	mov eax, DWORD PTR [esi+1336]
	mov edx, DWORD PTR [esi+1340]
	xor eax, DWORD PTR [esi+1368]
	xor edx, DWORD PTR [esi+1372]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1336], eax
	mov DWORD PTR [esi+1340], edx
	mov edx, DWORD PTR [esi+1320]
	mov eax, DWORD PTR [esi+1280]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1320]
	adc edx, DWORD PTR [esi+1324]
	add eax, DWORD PTR [esi+1280]
	adc edx, DWORD PTR [esi+1284]
	mov DWORD PTR [esi+1280], eax
	mov DWORD PTR [esi+1284], edx
	mov eax, DWORD PTR [esi+1400]
	mov edx, DWORD PTR [esi+1404]
	xor eax, DWORD PTR [esi+1280]
	xor edx, DWORD PTR [esi+1284]
	mov DWORD PTR [esi+1400], edx
	mov DWORD PTR [esi+1404], eax
	mov edx, DWORD PTR [esi+1400]
	mov eax, DWORD PTR [esi+1360]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1400]
	adc edx, DWORD PTR [esi+1404]
	add eax, DWORD PTR [esi+1360]
	adc edx, DWORD PTR [esi+1364]
	mov DWORD PTR [esi+1360], eax
	mov DWORD PTR [esi+1364], edx
	mov eax, DWORD PTR [esi+1320]
	mov edx, DWORD PTR [esi+1324]
	xor eax, DWORD PTR [esi+1360]
	xor edx, DWORD PTR [esi+1364]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1320], edx
	mov DWORD PTR [esi+1324], eax
	mov edx, DWORD PTR [esi+1320]
	mov eax, DWORD PTR [esi+1280]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1320]
	adc edx, DWORD PTR [esi+1324]
	add eax, DWORD PTR [esi+1280]
	adc edx, DWORD PTR [esi+1284]
	mov DWORD PTR [esi+1280], eax
	mov DWORD PTR [esi+1284], edx
	mov eax, DWORD PTR [esi+1400]
	mov edx, DWORD PTR [esi+1404]
	xor eax, DWORD PTR [esi+1280]
	xor edx, DWORD PTR [esi+1284]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1400], edx
	mov DWORD PTR [esi+1404], eax
	mov edx, DWORD PTR [esi+1400]
	mov eax, DWORD PTR [esi+1360]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1400]
	adc edx, DWORD PTR [esi+1404]
	add eax, DWORD PTR [esi+1360]
	adc edx, DWORD PTR [esi+1364]
	mov DWORD PTR [esi+1360], eax
	mov DWORD PTR [esi+1364], edx
	mov eax, DWORD PTR [esi+1320]
	mov edx, DWORD PTR [esi+1324]
	xor eax, DWORD PTR [esi+1360]
	xor edx, DWORD PTR [esi+1364]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1320], eax
	mov DWORD PTR [esi+1324], edx
	mov edx, DWORD PTR [esi+1328]
	mov eax, DWORD PTR [esi+1288]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1328]
	adc edx, DWORD PTR [esi+1332]
	add eax, DWORD PTR [esi+1288]
	adc edx, DWORD PTR [esi+1292]
	mov DWORD PTR [esi+1288], eax
	mov DWORD PTR [esi+1292], edx
	mov eax, DWORD PTR [esi+1376]
	mov edx, DWORD PTR [esi+1380]
	xor eax, DWORD PTR [esi+1288]
	xor edx, DWORD PTR [esi+1292]
	mov DWORD PTR [esi+1376], edx
	mov DWORD PTR [esi+1380], eax
	mov edx, DWORD PTR [esi+1376]
	mov eax, DWORD PTR [esi+1368]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1376]
	adc edx, DWORD PTR [esi+1380]
	add eax, DWORD PTR [esi+1368]
	adc edx, DWORD PTR [esi+1372]
	mov DWORD PTR [esi+1368], eax
	mov DWORD PTR [esi+1372], edx
	mov eax, DWORD PTR [esi+1328]
	mov edx, DWORD PTR [esi+1332]
	xor eax, DWORD PTR [esi+1368]
	xor edx, DWORD PTR [esi+1372]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1328], edx
	mov DWORD PTR [esi+1332], eax
	mov edx, DWORD PTR [esi+1328]
	mov eax, DWORD PTR [esi+1288]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1328]
	adc edx, DWORD PTR [esi+1332]
	add eax, DWORD PTR [esi+1288]
	adc edx, DWORD PTR [esi+1292]
	mov DWORD PTR [esi+1288], eax
	mov DWORD PTR [esi+1292], edx
	mov eax, DWORD PTR [esi+1376]
	mov edx, DWORD PTR [esi+1380]
	xor eax, DWORD PTR [esi+1288]
	xor edx, DWORD PTR [esi+1292]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1376], edx
	mov DWORD PTR [esi+1380], eax
	mov edx, DWORD PTR [esi+1376]
	mov eax, DWORD PTR [esi+1368]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1376]
	adc edx, DWORD PTR [esi+1380]
	add eax, DWORD PTR [esi+1368]
	adc edx, DWORD PTR [esi+1372]
	mov DWORD PTR [esi+1368], eax
	mov DWORD PTR [esi+1372], edx
	mov eax, DWORD PTR [esi+1328]
	mov edx, DWORD PTR [esi+1332]
	xor eax, DWORD PTR [esi+1368]
	xor edx, DWORD PTR [esi+1372]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1328], eax
	mov DWORD PTR [esi+1332], edx
	mov edx, DWORD PTR [esi+1336]
	mov eax, DWORD PTR [esi+1296]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1336]
	adc edx, DWORD PTR [esi+1340]
	add eax, DWORD PTR [esi+1296]
	adc edx, DWORD PTR [esi+1300]
	mov DWORD PTR [esi+1296], eax
	mov DWORD PTR [esi+1300], edx
	mov eax, DWORD PTR [esi+1384]
	mov edx, DWORD PTR [esi+1388]
	xor eax, DWORD PTR [esi+1296]
	xor edx, DWORD PTR [esi+1300]
	mov DWORD PTR [esi+1384], edx
	mov DWORD PTR [esi+1388], eax
	mov edx, DWORD PTR [esi+1384]
	mov eax, DWORD PTR [esi+1344]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1384]
	adc edx, DWORD PTR [esi+1388]
	add eax, DWORD PTR [esi+1344]
	adc edx, DWORD PTR [esi+1348]
	mov DWORD PTR [esi+1344], eax
	mov DWORD PTR [esi+1348], edx
	mov eax, DWORD PTR [esi+1336]
	mov edx, DWORD PTR [esi+1340]
	xor eax, DWORD PTR [esi+1344]
	xor edx, DWORD PTR [esi+1348]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1336], edx
	mov DWORD PTR [esi+1340], eax
	mov edx, DWORD PTR [esi+1336]
	mov eax, DWORD PTR [esi+1296]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1336]
	adc edx, DWORD PTR [esi+1340]
	add eax, DWORD PTR [esi+1296]
	adc edx, DWORD PTR [esi+1300]
	mov DWORD PTR [esi+1296], eax
	mov DWORD PTR [esi+1300], edx
	mov eax, DWORD PTR [esi+1384]
	mov edx, DWORD PTR [esi+1388]
	xor eax, DWORD PTR [esi+1296]
	xor edx, DWORD PTR [esi+1300]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1384], edx
	mov DWORD PTR [esi+1388], eax
	mov edx, DWORD PTR [esi+1384]
	mov eax, DWORD PTR [esi+1344]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1384]
	adc edx, DWORD PTR [esi+1388]
	add eax, DWORD PTR [esi+1344]
	adc edx, DWORD PTR [esi+1348]
	mov DWORD PTR [esi+1344], eax
	mov DWORD PTR [esi+1348], edx
	mov eax, DWORD PTR [esi+1336]
	mov edx, DWORD PTR [esi+1340]
	xor eax, DWORD PTR [esi+1344]
	xor edx, DWORD PTR [esi+1348]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1336], eax
	mov DWORD PTR [esi+1340], edx
	mov edx, DWORD PTR [esi+1312]
	mov eax, DWORD PTR [esi+1304]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1312]
	adc edx, DWORD PTR [esi+1316]
	add eax, DWORD PTR [esi+1304]
	adc edx, DWORD PTR [esi+1308]
	mov DWORD PTR [esi+1304], eax
	mov DWORD PTR [esi+1308], edx
	mov eax, DWORD PTR [esi+1392]
	mov edx, DWORD PTR [esi+1396]
	xor eax, DWORD PTR [esi+1304]
	xor edx, DWORD PTR [esi+1308]
	mov DWORD PTR [esi+1392], edx
	mov DWORD PTR [esi+1396], eax
	mov edx, DWORD PTR [esi+1392]
	mov eax, DWORD PTR [esi+1352]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1392]
	adc edx, DWORD PTR [esi+1396]
	add eax, DWORD PTR [esi+1352]
	adc edx, DWORD PTR [esi+1356]
	mov DWORD PTR [esi+1352], eax
	mov DWORD PTR [esi+1356], edx
	mov eax, DWORD PTR [esi+1312]
	mov edx, DWORD PTR [esi+1316]
	xor eax, DWORD PTR [esi+1352]
	xor edx, DWORD PTR [esi+1356]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1312], edx
	mov DWORD PTR [esi+1316], eax
	mov edx, DWORD PTR [esi+1312]
	mov eax, DWORD PTR [esi+1304]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1312]
	adc edx, DWORD PTR [esi+1316]
	add eax, DWORD PTR [esi+1304]
	adc edx, DWORD PTR [esi+1308]
	mov DWORD PTR [esi+1304], eax
	mov DWORD PTR [esi+1308], edx
	mov eax, DWORD PTR [esi+1392]
	mov edx, DWORD PTR [esi+1396]
	xor eax, DWORD PTR [esi+1304]
	xor edx, DWORD PTR [esi+1308]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1392], edx
	mov DWORD PTR [esi+1396], eax
	mov edx, DWORD PTR [esi+1392]
	mov eax, DWORD PTR [esi+1352]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1392]
	adc edx, DWORD PTR [esi+1396]
	add eax, DWORD PTR [esi+1352]
	adc edx, DWORD PTR [esi+1356]
	mov DWORD PTR [esi+1352], eax
	mov DWORD PTR [esi+1356], edx
	mov eax, DWORD PTR [esi+1312]
	mov edx, DWORD PTR [esi+1316]
	xor eax, DWORD PTR [esi+1352]
	xor edx, DWORD PTR [esi+1356]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1312], eax
	mov DWORD PTR [esi+1316], edx
	mov edx, DWORD PTR [esi+1440]
	mov eax, DWORD PTR [esi+1408]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1440]
	adc edx, DWORD PTR [esi+1444]
	add eax, DWORD PTR [esi+1408]
	adc edx, DWORD PTR [esi+1412]
	mov DWORD PTR [esi+1408], eax
	mov DWORD PTR [esi+1412], edx
	mov eax, DWORD PTR [esi+1504]
	mov edx, DWORD PTR [esi+1508]
	xor eax, DWORD PTR [esi+1408]
	xor edx, DWORD PTR [esi+1412]
	mov DWORD PTR [esi+1504], edx
	mov DWORD PTR [esi+1508], eax
	mov edx, DWORD PTR [esi+1504]
	mov eax, DWORD PTR [esi+1472]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1504]
	adc edx, DWORD PTR [esi+1508]
	add eax, DWORD PTR [esi+1472]
	adc edx, DWORD PTR [esi+1476]
	mov DWORD PTR [esi+1472], eax
	mov DWORD PTR [esi+1476], edx
	mov eax, DWORD PTR [esi+1440]
	mov edx, DWORD PTR [esi+1444]
	xor eax, DWORD PTR [esi+1472]
	xor edx, DWORD PTR [esi+1476]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1440], edx
	mov DWORD PTR [esi+1444], eax
	mov edx, DWORD PTR [esi+1440]
	mov eax, DWORD PTR [esi+1408]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1440]
	adc edx, DWORD PTR [esi+1444]
	add eax, DWORD PTR [esi+1408]
	adc edx, DWORD PTR [esi+1412]
	mov DWORD PTR [esi+1408], eax
	mov DWORD PTR [esi+1412], edx
	mov eax, DWORD PTR [esi+1504]
	mov edx, DWORD PTR [esi+1508]
	xor eax, DWORD PTR [esi+1408]
	xor edx, DWORD PTR [esi+1412]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1504], edx
	mov DWORD PTR [esi+1508], eax
	mov edx, DWORD PTR [esi+1504]
	mov eax, DWORD PTR [esi+1472]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1504]
	adc edx, DWORD PTR [esi+1508]
	add eax, DWORD PTR [esi+1472]
	adc edx, DWORD PTR [esi+1476]
	mov DWORD PTR [esi+1472], eax
	mov DWORD PTR [esi+1476], edx
	mov eax, DWORD PTR [esi+1440]
	mov edx, DWORD PTR [esi+1444]
	xor eax, DWORD PTR [esi+1472]
	xor edx, DWORD PTR [esi+1476]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1440], eax
	mov DWORD PTR [esi+1444], edx
	mov edx, DWORD PTR [esi+1448]
	mov eax, DWORD PTR [esi+1416]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1448]
	adc edx, DWORD PTR [esi+1452]
	add eax, DWORD PTR [esi+1416]
	adc edx, DWORD PTR [esi+1420]
	mov DWORD PTR [esi+1416], eax
	mov DWORD PTR [esi+1420], edx
	mov eax, DWORD PTR [esi+1512]
	mov edx, DWORD PTR [esi+1516]
	xor eax, DWORD PTR [esi+1416]
	xor edx, DWORD PTR [esi+1420]
	mov DWORD PTR [esi+1512], edx
	mov DWORD PTR [esi+1516], eax
	mov edx, DWORD PTR [esi+1512]
	mov eax, DWORD PTR [esi+1480]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1512]
	adc edx, DWORD PTR [esi+1516]
	add eax, DWORD PTR [esi+1480]
	adc edx, DWORD PTR [esi+1484]
	mov DWORD PTR [esi+1480], eax
	mov DWORD PTR [esi+1484], edx
	mov eax, DWORD PTR [esi+1448]
	mov edx, DWORD PTR [esi+1452]
	xor eax, DWORD PTR [esi+1480]
	xor edx, DWORD PTR [esi+1484]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1448], edx
	mov DWORD PTR [esi+1452], eax
	mov edx, DWORD PTR [esi+1448]
	mov eax, DWORD PTR [esi+1416]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1448]
	adc edx, DWORD PTR [esi+1452]
	add eax, DWORD PTR [esi+1416]
	adc edx, DWORD PTR [esi+1420]
	mov DWORD PTR [esi+1416], eax
	mov DWORD PTR [esi+1420], edx
	mov eax, DWORD PTR [esi+1512]
	mov edx, DWORD PTR [esi+1516]
	xor eax, DWORD PTR [esi+1416]
	xor edx, DWORD PTR [esi+1420]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1512], edx
	mov DWORD PTR [esi+1516], eax
	mov edx, DWORD PTR [esi+1512]
	mov eax, DWORD PTR [esi+1480]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1512]
	adc edx, DWORD PTR [esi+1516]
	add eax, DWORD PTR [esi+1480]
	adc edx, DWORD PTR [esi+1484]
	mov DWORD PTR [esi+1480], eax
	mov DWORD PTR [esi+1484], edx
	mov eax, DWORD PTR [esi+1448]
	mov edx, DWORD PTR [esi+1452]
	xor eax, DWORD PTR [esi+1480]
	xor edx, DWORD PTR [esi+1484]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1448], eax
	mov DWORD PTR [esi+1452], edx
	mov edx, DWORD PTR [esi+1456]
	mov eax, DWORD PTR [esi+1424]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1456]
	adc edx, DWORD PTR [esi+1460]
	add eax, DWORD PTR [esi+1424]
	adc edx, DWORD PTR [esi+1428]
	mov DWORD PTR [esi+1424], eax
	mov DWORD PTR [esi+1428], edx
	mov eax, DWORD PTR [esi+1520]
	mov edx, DWORD PTR [esi+1524]
	xor eax, DWORD PTR [esi+1424]
	xor edx, DWORD PTR [esi+1428]
	mov DWORD PTR [esi+1520], edx
	mov DWORD PTR [esi+1524], eax
	mov edx, DWORD PTR [esi+1520]
	mov eax, DWORD PTR [esi+1488]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1520]
	adc edx, DWORD PTR [esi+1524]
	add eax, DWORD PTR [esi+1488]
	adc edx, DWORD PTR [esi+1492]
	mov DWORD PTR [esi+1488], eax
	mov DWORD PTR [esi+1492], edx
	mov eax, DWORD PTR [esi+1456]
	mov edx, DWORD PTR [esi+1460]
	xor eax, DWORD PTR [esi+1488]
	xor edx, DWORD PTR [esi+1492]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1456], edx
	mov DWORD PTR [esi+1460], eax
	mov edx, DWORD PTR [esi+1456]
	mov eax, DWORD PTR [esi+1424]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1456]
	adc edx, DWORD PTR [esi+1460]
	add eax, DWORD PTR [esi+1424]
	adc edx, DWORD PTR [esi+1428]
	mov DWORD PTR [esi+1424], eax
	mov DWORD PTR [esi+1428], edx
	mov eax, DWORD PTR [esi+1520]
	mov edx, DWORD PTR [esi+1524]
	xor eax, DWORD PTR [esi+1424]
	xor edx, DWORD PTR [esi+1428]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1520], edx
	mov DWORD PTR [esi+1524], eax
	mov edx, DWORD PTR [esi+1520]
	mov eax, DWORD PTR [esi+1488]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1520]
	adc edx, DWORD PTR [esi+1524]
	add eax, DWORD PTR [esi+1488]
	adc edx, DWORD PTR [esi+1492]
	mov DWORD PTR [esi+1488], eax
	mov DWORD PTR [esi+1492], edx
	mov eax, DWORD PTR [esi+1456]
	mov edx, DWORD PTR [esi+1460]
	xor eax, DWORD PTR [esi+1488]
	xor edx, DWORD PTR [esi+1492]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1456], eax
	mov DWORD PTR [esi+1460], edx
	mov edx, DWORD PTR [esi+1464]
	mov eax, DWORD PTR [esi+1432]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1464]
	adc edx, DWORD PTR [esi+1468]
	add eax, DWORD PTR [esi+1432]
	adc edx, DWORD PTR [esi+1436]
	mov DWORD PTR [esi+1432], eax
	mov DWORD PTR [esi+1436], edx
	mov eax, DWORD PTR [esi+1528]
	mov edx, DWORD PTR [esi+1532]
	xor eax, DWORD PTR [esi+1432]
	xor edx, DWORD PTR [esi+1436]
	mov DWORD PTR [esi+1528], edx
	mov DWORD PTR [esi+1532], eax
	mov edx, DWORD PTR [esi+1528]
	mov eax, DWORD PTR [esi+1496]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1528]
	adc edx, DWORD PTR [esi+1532]
	add eax, DWORD PTR [esi+1496]
	adc edx, DWORD PTR [esi+1500]
	mov DWORD PTR [esi+1496], eax
	mov DWORD PTR [esi+1500], edx
	mov eax, DWORD PTR [esi+1464]
	mov edx, DWORD PTR [esi+1468]
	xor eax, DWORD PTR [esi+1496]
	xor edx, DWORD PTR [esi+1500]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1464], edx
	mov DWORD PTR [esi+1468], eax
	mov edx, DWORD PTR [esi+1464]
	mov eax, DWORD PTR [esi+1432]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1464]
	adc edx, DWORD PTR [esi+1468]
	add eax, DWORD PTR [esi+1432]
	adc edx, DWORD PTR [esi+1436]
	mov DWORD PTR [esi+1432], eax
	mov DWORD PTR [esi+1436], edx
	mov eax, DWORD PTR [esi+1528]
	mov edx, DWORD PTR [esi+1532]
	xor eax, DWORD PTR [esi+1432]
	xor edx, DWORD PTR [esi+1436]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1528], edx
	mov DWORD PTR [esi+1532], eax
	mov edx, DWORD PTR [esi+1528]
	mov eax, DWORD PTR [esi+1496]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1528]
	adc edx, DWORD PTR [esi+1532]
	add eax, DWORD PTR [esi+1496]
	adc edx, DWORD PTR [esi+1500]
	mov DWORD PTR [esi+1496], eax
	mov DWORD PTR [esi+1500], edx
	mov eax, DWORD PTR [esi+1464]
	mov edx, DWORD PTR [esi+1468]
	xor eax, DWORD PTR [esi+1496]
	xor edx, DWORD PTR [esi+1500]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1464], eax
	mov DWORD PTR [esi+1468], edx
	mov edx, DWORD PTR [esi+1448]
	mov eax, DWORD PTR [esi+1408]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1448]
	adc edx, DWORD PTR [esi+1452]
	add eax, DWORD PTR [esi+1408]
	adc edx, DWORD PTR [esi+1412]
	mov DWORD PTR [esi+1408], eax
	mov DWORD PTR [esi+1412], edx
	mov eax, DWORD PTR [esi+1528]
	mov edx, DWORD PTR [esi+1532]
	xor eax, DWORD PTR [esi+1408]
	xor edx, DWORD PTR [esi+1412]
	mov DWORD PTR [esi+1528], edx
	mov DWORD PTR [esi+1532], eax
	mov edx, DWORD PTR [esi+1528]
	mov eax, DWORD PTR [esi+1488]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1528]
	adc edx, DWORD PTR [esi+1532]
	add eax, DWORD PTR [esi+1488]
	adc edx, DWORD PTR [esi+1492]
	mov DWORD PTR [esi+1488], eax
	mov DWORD PTR [esi+1492], edx
	mov eax, DWORD PTR [esi+1448]
	mov edx, DWORD PTR [esi+1452]
	xor eax, DWORD PTR [esi+1488]
	xor edx, DWORD PTR [esi+1492]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1448], edx
	mov DWORD PTR [esi+1452], eax
	mov edx, DWORD PTR [esi+1448]
	mov eax, DWORD PTR [esi+1408]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1448]
	adc edx, DWORD PTR [esi+1452]
	add eax, DWORD PTR [esi+1408]
	adc edx, DWORD PTR [esi+1412]
	mov DWORD PTR [esi+1408], eax
	mov DWORD PTR [esi+1412], edx
	mov eax, DWORD PTR [esi+1528]
	mov edx, DWORD PTR [esi+1532]
	xor eax, DWORD PTR [esi+1408]
	xor edx, DWORD PTR [esi+1412]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1528], edx
	mov DWORD PTR [esi+1532], eax
	mov edx, DWORD PTR [esi+1528]
	mov eax, DWORD PTR [esi+1488]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1528]
	adc edx, DWORD PTR [esi+1532]
	add eax, DWORD PTR [esi+1488]
	adc edx, DWORD PTR [esi+1492]
	mov DWORD PTR [esi+1488], eax
	mov DWORD PTR [esi+1492], edx
	mov eax, DWORD PTR [esi+1448]
	mov edx, DWORD PTR [esi+1452]
	xor eax, DWORD PTR [esi+1488]
	xor edx, DWORD PTR [esi+1492]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1448], eax
	mov DWORD PTR [esi+1452], edx
	mov edx, DWORD PTR [esi+1456]
	mov eax, DWORD PTR [esi+1416]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1456]
	adc edx, DWORD PTR [esi+1460]
	add eax, DWORD PTR [esi+1416]
	adc edx, DWORD PTR [esi+1420]
	mov DWORD PTR [esi+1416], eax
	mov DWORD PTR [esi+1420], edx
	mov eax, DWORD PTR [esi+1504]
	mov edx, DWORD PTR [esi+1508]
	xor eax, DWORD PTR [esi+1416]
	xor edx, DWORD PTR [esi+1420]
	mov DWORD PTR [esi+1504], edx
	mov DWORD PTR [esi+1508], eax
	mov edx, DWORD PTR [esi+1504]
	mov eax, DWORD PTR [esi+1496]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1504]
	adc edx, DWORD PTR [esi+1508]
	add eax, DWORD PTR [esi+1496]
	adc edx, DWORD PTR [esi+1500]
	mov DWORD PTR [esi+1496], eax
	mov DWORD PTR [esi+1500], edx
	mov eax, DWORD PTR [esi+1456]
	mov edx, DWORD PTR [esi+1460]
	xor eax, DWORD PTR [esi+1496]
	xor edx, DWORD PTR [esi+1500]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1456], edx
	mov DWORD PTR [esi+1460], eax
	mov edx, DWORD PTR [esi+1456]
	mov eax, DWORD PTR [esi+1416]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1456]
	adc edx, DWORD PTR [esi+1460]
	add eax, DWORD PTR [esi+1416]
	adc edx, DWORD PTR [esi+1420]
	mov DWORD PTR [esi+1416], eax
	mov DWORD PTR [esi+1420], edx
	mov eax, DWORD PTR [esi+1504]
	mov edx, DWORD PTR [esi+1508]
	xor eax, DWORD PTR [esi+1416]
	xor edx, DWORD PTR [esi+1420]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1504], edx
	mov DWORD PTR [esi+1508], eax
	mov edx, DWORD PTR [esi+1504]
	mov eax, DWORD PTR [esi+1496]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1504]
	adc edx, DWORD PTR [esi+1508]
	add eax, DWORD PTR [esi+1496]
	adc edx, DWORD PTR [esi+1500]
	mov DWORD PTR [esi+1496], eax
	mov DWORD PTR [esi+1500], edx
	mov eax, DWORD PTR [esi+1456]
	mov edx, DWORD PTR [esi+1460]
	xor eax, DWORD PTR [esi+1496]
	xor edx, DWORD PTR [esi+1500]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1456], eax
	mov DWORD PTR [esi+1460], edx
	mov edx, DWORD PTR [esi+1464]
	mov eax, DWORD PTR [esi+1424]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1464]
	adc edx, DWORD PTR [esi+1468]
	add eax, DWORD PTR [esi+1424]
	adc edx, DWORD PTR [esi+1428]
	mov DWORD PTR [esi+1424], eax
	mov DWORD PTR [esi+1428], edx
	mov eax, DWORD PTR [esi+1512]
	mov edx, DWORD PTR [esi+1516]
	xor eax, DWORD PTR [esi+1424]
	xor edx, DWORD PTR [esi+1428]
	mov DWORD PTR [esi+1512], edx
	mov DWORD PTR [esi+1516], eax
	mov edx, DWORD PTR [esi+1512]
	mov eax, DWORD PTR [esi+1472]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1512]
	adc edx, DWORD PTR [esi+1516]
	add eax, DWORD PTR [esi+1472]
	adc edx, DWORD PTR [esi+1476]
	mov DWORD PTR [esi+1472], eax
	mov DWORD PTR [esi+1476], edx
	mov eax, DWORD PTR [esi+1464]
	mov edx, DWORD PTR [esi+1468]
	xor eax, DWORD PTR [esi+1472]
	xor edx, DWORD PTR [esi+1476]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1464], edx
	mov DWORD PTR [esi+1468], eax
	mov edx, DWORD PTR [esi+1464]
	mov eax, DWORD PTR [esi+1424]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1464]
	adc edx, DWORD PTR [esi+1468]
	add eax, DWORD PTR [esi+1424]
	adc edx, DWORD PTR [esi+1428]
	mov DWORD PTR [esi+1424], eax
	mov DWORD PTR [esi+1428], edx
	mov eax, DWORD PTR [esi+1512]
	mov edx, DWORD PTR [esi+1516]
	xor eax, DWORD PTR [esi+1424]
	xor edx, DWORD PTR [esi+1428]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1512], edx
	mov DWORD PTR [esi+1516], eax
	mov edx, DWORD PTR [esi+1512]
	mov eax, DWORD PTR [esi+1472]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1512]
	adc edx, DWORD PTR [esi+1516]
	add eax, DWORD PTR [esi+1472]
	adc edx, DWORD PTR [esi+1476]
	mov DWORD PTR [esi+1472], eax
	mov DWORD PTR [esi+1476], edx
	mov eax, DWORD PTR [esi+1464]
	mov edx, DWORD PTR [esi+1468]
	xor eax, DWORD PTR [esi+1472]
	xor edx, DWORD PTR [esi+1476]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1464], eax
	mov DWORD PTR [esi+1468], edx
	mov edx, DWORD PTR [esi+1440]
	mov eax, DWORD PTR [esi+1432]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1440]
	adc edx, DWORD PTR [esi+1444]
	add eax, DWORD PTR [esi+1432]
	adc edx, DWORD PTR [esi+1436]
	mov DWORD PTR [esi+1432], eax
	mov DWORD PTR [esi+1436], edx
	mov eax, DWORD PTR [esi+1520]
	mov edx, DWORD PTR [esi+1524]
	xor eax, DWORD PTR [esi+1432]
	xor edx, DWORD PTR [esi+1436]
	mov DWORD PTR [esi+1520], edx
	mov DWORD PTR [esi+1524], eax
	mov edx, DWORD PTR [esi+1520]
	mov eax, DWORD PTR [esi+1480]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1520]
	adc edx, DWORD PTR [esi+1524]
	add eax, DWORD PTR [esi+1480]
	adc edx, DWORD PTR [esi+1484]
	mov DWORD PTR [esi+1480], eax
	mov DWORD PTR [esi+1484], edx
	mov eax, DWORD PTR [esi+1440]
	mov edx, DWORD PTR [esi+1444]
	xor eax, DWORD PTR [esi+1480]
	xor edx, DWORD PTR [esi+1484]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1440], edx
	mov DWORD PTR [esi+1444], eax
	mov edx, DWORD PTR [esi+1440]
	mov eax, DWORD PTR [esi+1432]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1440]
	adc edx, DWORD PTR [esi+1444]
	add eax, DWORD PTR [esi+1432]
	adc edx, DWORD PTR [esi+1436]
	mov DWORD PTR [esi+1432], eax
	mov DWORD PTR [esi+1436], edx
	mov eax, DWORD PTR [esi+1520]
	mov edx, DWORD PTR [esi+1524]
	xor eax, DWORD PTR [esi+1432]
	xor edx, DWORD PTR [esi+1436]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1520], edx
	mov DWORD PTR [esi+1524], eax
	mov edx, DWORD PTR [esi+1520]
	mov eax, DWORD PTR [esi+1480]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1520]
	adc edx, DWORD PTR [esi+1524]
	add eax, DWORD PTR [esi+1480]
	adc edx, DWORD PTR [esi+1484]
	mov DWORD PTR [esi+1480], eax
	mov DWORD PTR [esi+1484], edx
	mov eax, DWORD PTR [esi+1440]
	mov edx, DWORD PTR [esi+1444]
	xor eax, DWORD PTR [esi+1480]
	xor edx, DWORD PTR [esi+1484]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1440], eax
	mov DWORD PTR [esi+1444], edx
	mov edx, DWORD PTR [esi+1568]
	mov eax, DWORD PTR [esi+1536]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1568]
	adc edx, DWORD PTR [esi+1572]
	add eax, DWORD PTR [esi+1536]
	adc edx, DWORD PTR [esi+1540]
	mov DWORD PTR [esi+1536], eax
	mov DWORD PTR [esi+1540], edx
	mov eax, DWORD PTR [esi+1632]
	mov edx, DWORD PTR [esi+1636]
	xor eax, DWORD PTR [esi+1536]
	xor edx, DWORD PTR [esi+1540]
	mov DWORD PTR [esi+1632], edx
	mov DWORD PTR [esi+1636], eax
	mov edx, DWORD PTR [esi+1632]
	mov eax, DWORD PTR [esi+1600]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1632]
	adc edx, DWORD PTR [esi+1636]
	add eax, DWORD PTR [esi+1600]
	adc edx, DWORD PTR [esi+1604]
	mov DWORD PTR [esi+1600], eax
	mov DWORD PTR [esi+1604], edx
	mov eax, DWORD PTR [esi+1568]
	mov edx, DWORD PTR [esi+1572]
	xor eax, DWORD PTR [esi+1600]
	xor edx, DWORD PTR [esi+1604]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1568], edx
	mov DWORD PTR [esi+1572], eax
	mov edx, DWORD PTR [esi+1568]
	mov eax, DWORD PTR [esi+1536]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1568]
	adc edx, DWORD PTR [esi+1572]
	add eax, DWORD PTR [esi+1536]
	adc edx, DWORD PTR [esi+1540]
	mov DWORD PTR [esi+1536], eax
	mov DWORD PTR [esi+1540], edx
	mov eax, DWORD PTR [esi+1632]
	mov edx, DWORD PTR [esi+1636]
	xor eax, DWORD PTR [esi+1536]
	xor edx, DWORD PTR [esi+1540]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1632], edx
	mov DWORD PTR [esi+1636], eax
	mov edx, DWORD PTR [esi+1632]
	mov eax, DWORD PTR [esi+1600]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1632]
	adc edx, DWORD PTR [esi+1636]
	add eax, DWORD PTR [esi+1600]
	adc edx, DWORD PTR [esi+1604]
	mov DWORD PTR [esi+1600], eax
	mov DWORD PTR [esi+1604], edx
	mov eax, DWORD PTR [esi+1568]
	mov edx, DWORD PTR [esi+1572]
	xor eax, DWORD PTR [esi+1600]
	xor edx, DWORD PTR [esi+1604]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1568], eax
	mov DWORD PTR [esi+1572], edx
	mov edx, DWORD PTR [esi+1576]
	mov eax, DWORD PTR [esi+1544]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1576]
	adc edx, DWORD PTR [esi+1580]
	add eax, DWORD PTR [esi+1544]
	adc edx, DWORD PTR [esi+1548]
	mov DWORD PTR [esi+1544], eax
	mov DWORD PTR [esi+1548], edx
	mov eax, DWORD PTR [esi+1640]
	mov edx, DWORD PTR [esi+1644]
	xor eax, DWORD PTR [esi+1544]
	xor edx, DWORD PTR [esi+1548]
	mov DWORD PTR [esi+1640], edx
	mov DWORD PTR [esi+1644], eax
	mov edx, DWORD PTR [esi+1640]
	mov eax, DWORD PTR [esi+1608]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1640]
	adc edx, DWORD PTR [esi+1644]
	add eax, DWORD PTR [esi+1608]
	adc edx, DWORD PTR [esi+1612]
	mov DWORD PTR [esi+1608], eax
	mov DWORD PTR [esi+1612], edx
	mov eax, DWORD PTR [esi+1576]
	mov edx, DWORD PTR [esi+1580]
	xor eax, DWORD PTR [esi+1608]
	xor edx, DWORD PTR [esi+1612]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1576], edx
	mov DWORD PTR [esi+1580], eax
	mov edx, DWORD PTR [esi+1576]
	mov eax, DWORD PTR [esi+1544]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1576]
	adc edx, DWORD PTR [esi+1580]
	add eax, DWORD PTR [esi+1544]
	adc edx, DWORD PTR [esi+1548]
	mov DWORD PTR [esi+1544], eax
	mov DWORD PTR [esi+1548], edx
	mov eax, DWORD PTR [esi+1640]
	mov edx, DWORD PTR [esi+1644]
	xor eax, DWORD PTR [esi+1544]
	xor edx, DWORD PTR [esi+1548]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1640], edx
	mov DWORD PTR [esi+1644], eax
	mov edx, DWORD PTR [esi+1640]
	mov eax, DWORD PTR [esi+1608]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1640]
	adc edx, DWORD PTR [esi+1644]
	add eax, DWORD PTR [esi+1608]
	adc edx, DWORD PTR [esi+1612]
	mov DWORD PTR [esi+1608], eax
	mov DWORD PTR [esi+1612], edx
	mov eax, DWORD PTR [esi+1576]
	mov edx, DWORD PTR [esi+1580]
	xor eax, DWORD PTR [esi+1608]
	xor edx, DWORD PTR [esi+1612]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1576], eax
	mov DWORD PTR [esi+1580], edx
	mov edx, DWORD PTR [esi+1584]
	mov eax, DWORD PTR [esi+1552]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1584]
	adc edx, DWORD PTR [esi+1588]
	add eax, DWORD PTR [esi+1552]
	adc edx, DWORD PTR [esi+1556]
	mov DWORD PTR [esi+1552], eax
	mov DWORD PTR [esi+1556], edx
	mov eax, DWORD PTR [esi+1648]
	mov edx, DWORD PTR [esi+1652]
	xor eax, DWORD PTR [esi+1552]
	xor edx, DWORD PTR [esi+1556]
	mov DWORD PTR [esi+1648], edx
	mov DWORD PTR [esi+1652], eax
	mov edx, DWORD PTR [esi+1648]
	mov eax, DWORD PTR [esi+1616]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1648]
	adc edx, DWORD PTR [esi+1652]
	add eax, DWORD PTR [esi+1616]
	adc edx, DWORD PTR [esi+1620]
	mov DWORD PTR [esi+1616], eax
	mov DWORD PTR [esi+1620], edx
	mov eax, DWORD PTR [esi+1584]
	mov edx, DWORD PTR [esi+1588]
	xor eax, DWORD PTR [esi+1616]
	xor edx, DWORD PTR [esi+1620]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1584], edx
	mov DWORD PTR [esi+1588], eax
	mov edx, DWORD PTR [esi+1584]
	mov eax, DWORD PTR [esi+1552]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1584]
	adc edx, DWORD PTR [esi+1588]
	add eax, DWORD PTR [esi+1552]
	adc edx, DWORD PTR [esi+1556]
	mov DWORD PTR [esi+1552], eax
	mov DWORD PTR [esi+1556], edx
	mov eax, DWORD PTR [esi+1648]
	mov edx, DWORD PTR [esi+1652]
	xor eax, DWORD PTR [esi+1552]
	xor edx, DWORD PTR [esi+1556]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1648], edx
	mov DWORD PTR [esi+1652], eax
	mov edx, DWORD PTR [esi+1648]
	mov eax, DWORD PTR [esi+1616]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1648]
	adc edx, DWORD PTR [esi+1652]
	add eax, DWORD PTR [esi+1616]
	adc edx, DWORD PTR [esi+1620]
	mov DWORD PTR [esi+1616], eax
	mov DWORD PTR [esi+1620], edx
	mov eax, DWORD PTR [esi+1584]
	mov edx, DWORD PTR [esi+1588]
	xor eax, DWORD PTR [esi+1616]
	xor edx, DWORD PTR [esi+1620]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1584], eax
	mov DWORD PTR [esi+1588], edx
	mov edx, DWORD PTR [esi+1592]
	mov eax, DWORD PTR [esi+1560]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1592]
	adc edx, DWORD PTR [esi+1596]
	add eax, DWORD PTR [esi+1560]
	adc edx, DWORD PTR [esi+1564]
	mov DWORD PTR [esi+1560], eax
	mov DWORD PTR [esi+1564], edx
	mov eax, DWORD PTR [esi+1656]
	mov edx, DWORD PTR [esi+1660]
	xor eax, DWORD PTR [esi+1560]
	xor edx, DWORD PTR [esi+1564]
	mov DWORD PTR [esi+1656], edx
	mov DWORD PTR [esi+1660], eax
	mov edx, DWORD PTR [esi+1656]
	mov eax, DWORD PTR [esi+1624]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1656]
	adc edx, DWORD PTR [esi+1660]
	add eax, DWORD PTR [esi+1624]
	adc edx, DWORD PTR [esi+1628]
	mov DWORD PTR [esi+1624], eax
	mov DWORD PTR [esi+1628], edx
	mov eax, DWORD PTR [esi+1592]
	mov edx, DWORD PTR [esi+1596]
	xor eax, DWORD PTR [esi+1624]
	xor edx, DWORD PTR [esi+1628]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1592], edx
	mov DWORD PTR [esi+1596], eax
	mov edx, DWORD PTR [esi+1592]
	mov eax, DWORD PTR [esi+1560]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1592]
	adc edx, DWORD PTR [esi+1596]
	add eax, DWORD PTR [esi+1560]
	adc edx, DWORD PTR [esi+1564]
	mov DWORD PTR [esi+1560], eax
	mov DWORD PTR [esi+1564], edx
	mov eax, DWORD PTR [esi+1656]
	mov edx, DWORD PTR [esi+1660]
	xor eax, DWORD PTR [esi+1560]
	xor edx, DWORD PTR [esi+1564]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1656], edx
	mov DWORD PTR [esi+1660], eax
	mov edx, DWORD PTR [esi+1656]
	mov eax, DWORD PTR [esi+1624]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1656]
	adc edx, DWORD PTR [esi+1660]
	add eax, DWORD PTR [esi+1624]
	adc edx, DWORD PTR [esi+1628]
	mov DWORD PTR [esi+1624], eax
	mov DWORD PTR [esi+1628], edx
	mov eax, DWORD PTR [esi+1592]
	mov edx, DWORD PTR [esi+1596]
	xor eax, DWORD PTR [esi+1624]
	xor edx, DWORD PTR [esi+1628]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1592], eax
	mov DWORD PTR [esi+1596], edx
	mov edx, DWORD PTR [esi+1576]
	mov eax, DWORD PTR [esi+1536]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1576]
	adc edx, DWORD PTR [esi+1580]
	add eax, DWORD PTR [esi+1536]
	adc edx, DWORD PTR [esi+1540]
	mov DWORD PTR [esi+1536], eax
	mov DWORD PTR [esi+1540], edx
	mov eax, DWORD PTR [esi+1656]
	mov edx, DWORD PTR [esi+1660]
	xor eax, DWORD PTR [esi+1536]
	xor edx, DWORD PTR [esi+1540]
	mov DWORD PTR [esi+1656], edx
	mov DWORD PTR [esi+1660], eax
	mov edx, DWORD PTR [esi+1656]
	mov eax, DWORD PTR [esi+1616]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1656]
	adc edx, DWORD PTR [esi+1660]
	add eax, DWORD PTR [esi+1616]
	adc edx, DWORD PTR [esi+1620]
	mov DWORD PTR [esi+1616], eax
	mov DWORD PTR [esi+1620], edx
	mov eax, DWORD PTR [esi+1576]
	mov edx, DWORD PTR [esi+1580]
	xor eax, DWORD PTR [esi+1616]
	xor edx, DWORD PTR [esi+1620]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1576], edx
	mov DWORD PTR [esi+1580], eax
	mov edx, DWORD PTR [esi+1576]
	mov eax, DWORD PTR [esi+1536]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1576]
	adc edx, DWORD PTR [esi+1580]
	add eax, DWORD PTR [esi+1536]
	adc edx, DWORD PTR [esi+1540]
	mov DWORD PTR [esi+1536], eax
	mov DWORD PTR [esi+1540], edx
	mov eax, DWORD PTR [esi+1656]
	mov edx, DWORD PTR [esi+1660]
	xor eax, DWORD PTR [esi+1536]
	xor edx, DWORD PTR [esi+1540]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1656], edx
	mov DWORD PTR [esi+1660], eax
	mov edx, DWORD PTR [esi+1656]
	mov eax, DWORD PTR [esi+1616]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1656]
	adc edx, DWORD PTR [esi+1660]
	add eax, DWORD PTR [esi+1616]
	adc edx, DWORD PTR [esi+1620]
	mov DWORD PTR [esi+1616], eax
	mov DWORD PTR [esi+1620], edx
	mov eax, DWORD PTR [esi+1576]
	mov edx, DWORD PTR [esi+1580]
	xor eax, DWORD PTR [esi+1616]
	xor edx, DWORD PTR [esi+1620]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1576], eax
	mov DWORD PTR [esi+1580], edx
	mov edx, DWORD PTR [esi+1584]
	mov eax, DWORD PTR [esi+1544]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1584]
	adc edx, DWORD PTR [esi+1588]
	add eax, DWORD PTR [esi+1544]
	adc edx, DWORD PTR [esi+1548]
	mov DWORD PTR [esi+1544], eax
	mov DWORD PTR [esi+1548], edx
	mov eax, DWORD PTR [esi+1632]
	mov edx, DWORD PTR [esi+1636]
	xor eax, DWORD PTR [esi+1544]
	xor edx, DWORD PTR [esi+1548]
	mov DWORD PTR [esi+1632], edx
	mov DWORD PTR [esi+1636], eax
	mov edx, DWORD PTR [esi+1632]
	mov eax, DWORD PTR [esi+1624]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1632]
	adc edx, DWORD PTR [esi+1636]
	add eax, DWORD PTR [esi+1624]
	adc edx, DWORD PTR [esi+1628]
	mov DWORD PTR [esi+1624], eax
	mov DWORD PTR [esi+1628], edx
	mov eax, DWORD PTR [esi+1584]
	mov edx, DWORD PTR [esi+1588]
	xor eax, DWORD PTR [esi+1624]
	xor edx, DWORD PTR [esi+1628]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1584], edx
	mov DWORD PTR [esi+1588], eax
	mov edx, DWORD PTR [esi+1584]
	mov eax, DWORD PTR [esi+1544]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1584]
	adc edx, DWORD PTR [esi+1588]
	add eax, DWORD PTR [esi+1544]
	adc edx, DWORD PTR [esi+1548]
	mov DWORD PTR [esi+1544], eax
	mov DWORD PTR [esi+1548], edx
	mov eax, DWORD PTR [esi+1632]
	mov edx, DWORD PTR [esi+1636]
	xor eax, DWORD PTR [esi+1544]
	xor edx, DWORD PTR [esi+1548]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1632], edx
	mov DWORD PTR [esi+1636], eax
	mov edx, DWORD PTR [esi+1632]
	mov eax, DWORD PTR [esi+1624]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1632]
	adc edx, DWORD PTR [esi+1636]
	add eax, DWORD PTR [esi+1624]
	adc edx, DWORD PTR [esi+1628]
	mov DWORD PTR [esi+1624], eax
	mov DWORD PTR [esi+1628], edx
	mov eax, DWORD PTR [esi+1584]
	mov edx, DWORD PTR [esi+1588]
	xor eax, DWORD PTR [esi+1624]
	xor edx, DWORD PTR [esi+1628]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1584], eax
	mov DWORD PTR [esi+1588], edx
	mov edx, DWORD PTR [esi+1592]
	mov eax, DWORD PTR [esi+1552]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1592]
	adc edx, DWORD PTR [esi+1596]
	add eax, DWORD PTR [esi+1552]
	adc edx, DWORD PTR [esi+1556]
	mov DWORD PTR [esi+1552], eax
	mov DWORD PTR [esi+1556], edx
	mov eax, DWORD PTR [esi+1640]
	mov edx, DWORD PTR [esi+1644]
	xor eax, DWORD PTR [esi+1552]
	xor edx, DWORD PTR [esi+1556]
	mov DWORD PTR [esi+1640], edx
	mov DWORD PTR [esi+1644], eax
	mov edx, DWORD PTR [esi+1640]
	mov eax, DWORD PTR [esi+1600]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1640]
	adc edx, DWORD PTR [esi+1644]
	add eax, DWORD PTR [esi+1600]
	adc edx, DWORD PTR [esi+1604]
	mov DWORD PTR [esi+1600], eax
	mov DWORD PTR [esi+1604], edx
	mov eax, DWORD PTR [esi+1592]
	mov edx, DWORD PTR [esi+1596]
	xor eax, DWORD PTR [esi+1600]
	xor edx, DWORD PTR [esi+1604]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1592], edx
	mov DWORD PTR [esi+1596], eax
	mov edx, DWORD PTR [esi+1592]
	mov eax, DWORD PTR [esi+1552]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1592]
	adc edx, DWORD PTR [esi+1596]
	add eax, DWORD PTR [esi+1552]
	adc edx, DWORD PTR [esi+1556]
	mov DWORD PTR [esi+1552], eax
	mov DWORD PTR [esi+1556], edx
	mov eax, DWORD PTR [esi+1640]
	mov edx, DWORD PTR [esi+1644]
	xor eax, DWORD PTR [esi+1552]
	xor edx, DWORD PTR [esi+1556]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1640], edx
	mov DWORD PTR [esi+1644], eax
	mov edx, DWORD PTR [esi+1640]
	mov eax, DWORD PTR [esi+1600]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1640]
	adc edx, DWORD PTR [esi+1644]
	add eax, DWORD PTR [esi+1600]
	adc edx, DWORD PTR [esi+1604]
	mov DWORD PTR [esi+1600], eax
	mov DWORD PTR [esi+1604], edx
	mov eax, DWORD PTR [esi+1592]
	mov edx, DWORD PTR [esi+1596]
	xor eax, DWORD PTR [esi+1600]
	xor edx, DWORD PTR [esi+1604]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1592], eax
	mov DWORD PTR [esi+1596], edx
	mov edx, DWORD PTR [esi+1568]
	mov eax, DWORD PTR [esi+1560]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1568]
	adc edx, DWORD PTR [esi+1572]
	add eax, DWORD PTR [esi+1560]
	adc edx, DWORD PTR [esi+1564]
	mov DWORD PTR [esi+1560], eax
	mov DWORD PTR [esi+1564], edx
	mov eax, DWORD PTR [esi+1648]
	mov edx, DWORD PTR [esi+1652]
	xor eax, DWORD PTR [esi+1560]
	xor edx, DWORD PTR [esi+1564]
	mov DWORD PTR [esi+1648], edx
	mov DWORD PTR [esi+1652], eax
	mov edx, DWORD PTR [esi+1648]
	mov eax, DWORD PTR [esi+1608]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1648]
	adc edx, DWORD PTR [esi+1652]
	add eax, DWORD PTR [esi+1608]
	adc edx, DWORD PTR [esi+1612]
	mov DWORD PTR [esi+1608], eax
	mov DWORD PTR [esi+1612], edx
	mov eax, DWORD PTR [esi+1568]
	mov edx, DWORD PTR [esi+1572]
	xor eax, DWORD PTR [esi+1608]
	xor edx, DWORD PTR [esi+1612]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1568], edx
	mov DWORD PTR [esi+1572], eax
	mov edx, DWORD PTR [esi+1568]
	mov eax, DWORD PTR [esi+1560]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1568]
	adc edx, DWORD PTR [esi+1572]
	add eax, DWORD PTR [esi+1560]
	adc edx, DWORD PTR [esi+1564]
	mov DWORD PTR [esi+1560], eax
	mov DWORD PTR [esi+1564], edx
	mov eax, DWORD PTR [esi+1648]
	mov edx, DWORD PTR [esi+1652]
	xor eax, DWORD PTR [esi+1560]
	xor edx, DWORD PTR [esi+1564]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1648], edx
	mov DWORD PTR [esi+1652], eax
	mov edx, DWORD PTR [esi+1648]
	mov eax, DWORD PTR [esi+1608]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1648]
	adc edx, DWORD PTR [esi+1652]
	add eax, DWORD PTR [esi+1608]
	adc edx, DWORD PTR [esi+1612]
	mov DWORD PTR [esi+1608], eax
	mov DWORD PTR [esi+1612], edx
	mov eax, DWORD PTR [esi+1568]
	mov edx, DWORD PTR [esi+1572]
	xor eax, DWORD PTR [esi+1608]
	xor edx, DWORD PTR [esi+1612]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1568], eax
	mov DWORD PTR [esi+1572], edx
	mov edx, DWORD PTR [esi+1696]
	mov eax, DWORD PTR [esi+1664]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1696]
	adc edx, DWORD PTR [esi+1700]
	add eax, DWORD PTR [esi+1664]
	adc edx, DWORD PTR [esi+1668]
	mov DWORD PTR [esi+1664], eax
	mov DWORD PTR [esi+1668], edx
	mov eax, DWORD PTR [esi+1760]
	mov edx, DWORD PTR [esi+1764]
	xor eax, DWORD PTR [esi+1664]
	xor edx, DWORD PTR [esi+1668]
	mov DWORD PTR [esi+1760], edx
	mov DWORD PTR [esi+1764], eax
	mov edx, DWORD PTR [esi+1760]
	mov eax, DWORD PTR [esi+1728]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1760]
	adc edx, DWORD PTR [esi+1764]
	add eax, DWORD PTR [esi+1728]
	adc edx, DWORD PTR [esi+1732]
	mov DWORD PTR [esi+1728], eax
	mov DWORD PTR [esi+1732], edx
	mov eax, DWORD PTR [esi+1696]
	mov edx, DWORD PTR [esi+1700]
	xor eax, DWORD PTR [esi+1728]
	xor edx, DWORD PTR [esi+1732]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1696], edx
	mov DWORD PTR [esi+1700], eax
	mov edx, DWORD PTR [esi+1696]
	mov eax, DWORD PTR [esi+1664]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1696]
	adc edx, DWORD PTR [esi+1700]
	add eax, DWORD PTR [esi+1664]
	adc edx, DWORD PTR [esi+1668]
	mov DWORD PTR [esi+1664], eax
	mov DWORD PTR [esi+1668], edx
	mov eax, DWORD PTR [esi+1760]
	mov edx, DWORD PTR [esi+1764]
	xor eax, DWORD PTR [esi+1664]
	xor edx, DWORD PTR [esi+1668]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1760], edx
	mov DWORD PTR [esi+1764], eax
	mov edx, DWORD PTR [esi+1760]
	mov eax, DWORD PTR [esi+1728]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1760]
	adc edx, DWORD PTR [esi+1764]
	add eax, DWORD PTR [esi+1728]
	adc edx, DWORD PTR [esi+1732]
	mov DWORD PTR [esi+1728], eax
	mov DWORD PTR [esi+1732], edx
	mov eax, DWORD PTR [esi+1696]
	mov edx, DWORD PTR [esi+1700]
	xor eax, DWORD PTR [esi+1728]
	xor edx, DWORD PTR [esi+1732]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1696], eax
	mov DWORD PTR [esi+1700], edx
	mov edx, DWORD PTR [esi+1704]
	mov eax, DWORD PTR [esi+1672]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1704]
	adc edx, DWORD PTR [esi+1708]
	add eax, DWORD PTR [esi+1672]
	adc edx, DWORD PTR [esi+1676]
	mov DWORD PTR [esi+1672], eax
	mov DWORD PTR [esi+1676], edx
	mov eax, DWORD PTR [esi+1768]
	mov edx, DWORD PTR [esi+1772]
	xor eax, DWORD PTR [esi+1672]
	xor edx, DWORD PTR [esi+1676]
	mov DWORD PTR [esi+1768], edx
	mov DWORD PTR [esi+1772], eax
	mov edx, DWORD PTR [esi+1768]
	mov eax, DWORD PTR [esi+1736]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1768]
	adc edx, DWORD PTR [esi+1772]
	add eax, DWORD PTR [esi+1736]
	adc edx, DWORD PTR [esi+1740]
	mov DWORD PTR [esi+1736], eax
	mov DWORD PTR [esi+1740], edx
	mov eax, DWORD PTR [esi+1704]
	mov edx, DWORD PTR [esi+1708]
	xor eax, DWORD PTR [esi+1736]
	xor edx, DWORD PTR [esi+1740]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1704], edx
	mov DWORD PTR [esi+1708], eax
	mov edx, DWORD PTR [esi+1704]
	mov eax, DWORD PTR [esi+1672]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1704]
	adc edx, DWORD PTR [esi+1708]
	add eax, DWORD PTR [esi+1672]
	adc edx, DWORD PTR [esi+1676]
	mov DWORD PTR [esi+1672], eax
	mov DWORD PTR [esi+1676], edx
	mov eax, DWORD PTR [esi+1768]
	mov edx, DWORD PTR [esi+1772]
	xor eax, DWORD PTR [esi+1672]
	xor edx, DWORD PTR [esi+1676]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1768], edx
	mov DWORD PTR [esi+1772], eax
	mov edx, DWORD PTR [esi+1768]
	mov eax, DWORD PTR [esi+1736]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1768]
	adc edx, DWORD PTR [esi+1772]
	add eax, DWORD PTR [esi+1736]
	adc edx, DWORD PTR [esi+1740]
	mov DWORD PTR [esi+1736], eax
	mov DWORD PTR [esi+1740], edx
	mov eax, DWORD PTR [esi+1704]
	mov edx, DWORD PTR [esi+1708]
	xor eax, DWORD PTR [esi+1736]
	xor edx, DWORD PTR [esi+1740]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1704], eax
	mov DWORD PTR [esi+1708], edx
	mov edx, DWORD PTR [esi+1712]
	mov eax, DWORD PTR [esi+1680]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1712]
	adc edx, DWORD PTR [esi+1716]
	add eax, DWORD PTR [esi+1680]
	adc edx, DWORD PTR [esi+1684]
	mov DWORD PTR [esi+1680], eax
	mov DWORD PTR [esi+1684], edx
	mov eax, DWORD PTR [esi+1776]
	mov edx, DWORD PTR [esi+1780]
	xor eax, DWORD PTR [esi+1680]
	xor edx, DWORD PTR [esi+1684]
	mov DWORD PTR [esi+1776], edx
	mov DWORD PTR [esi+1780], eax
	mov edx, DWORD PTR [esi+1776]
	mov eax, DWORD PTR [esi+1744]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1776]
	adc edx, DWORD PTR [esi+1780]
	add eax, DWORD PTR [esi+1744]
	adc edx, DWORD PTR [esi+1748]
	mov DWORD PTR [esi+1744], eax
	mov DWORD PTR [esi+1748], edx
	mov eax, DWORD PTR [esi+1712]
	mov edx, DWORD PTR [esi+1716]
	xor eax, DWORD PTR [esi+1744]
	xor edx, DWORD PTR [esi+1748]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1712], edx
	mov DWORD PTR [esi+1716], eax
	mov edx, DWORD PTR [esi+1712]
	mov eax, DWORD PTR [esi+1680]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1712]
	adc edx, DWORD PTR [esi+1716]
	add eax, DWORD PTR [esi+1680]
	adc edx, DWORD PTR [esi+1684]
	mov DWORD PTR [esi+1680], eax
	mov DWORD PTR [esi+1684], edx
	mov eax, DWORD PTR [esi+1776]
	mov edx, DWORD PTR [esi+1780]
	xor eax, DWORD PTR [esi+1680]
	xor edx, DWORD PTR [esi+1684]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1776], edx
	mov DWORD PTR [esi+1780], eax
	mov edx, DWORD PTR [esi+1776]
	mov eax, DWORD PTR [esi+1744]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1776]
	adc edx, DWORD PTR [esi+1780]
	add eax, DWORD PTR [esi+1744]
	adc edx, DWORD PTR [esi+1748]
	mov DWORD PTR [esi+1744], eax
	mov DWORD PTR [esi+1748], edx
	mov eax, DWORD PTR [esi+1712]
	mov edx, DWORD PTR [esi+1716]
	xor eax, DWORD PTR [esi+1744]
	xor edx, DWORD PTR [esi+1748]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1712], eax
	mov DWORD PTR [esi+1716], edx
	mov edx, DWORD PTR [esi+1720]
	mov eax, DWORD PTR [esi+1688]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1720]
	adc edx, DWORD PTR [esi+1724]
	add eax, DWORD PTR [esi+1688]
	adc edx, DWORD PTR [esi+1692]
	mov DWORD PTR [esi+1688], eax
	mov DWORD PTR [esi+1692], edx
	mov eax, DWORD PTR [esi+1784]
	mov edx, DWORD PTR [esi+1788]
	xor eax, DWORD PTR [esi+1688]
	xor edx, DWORD PTR [esi+1692]
	mov DWORD PTR [esi+1784], edx
	mov DWORD PTR [esi+1788], eax
	mov edx, DWORD PTR [esi+1784]
	mov eax, DWORD PTR [esi+1752]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1784]
	adc edx, DWORD PTR [esi+1788]
	add eax, DWORD PTR [esi+1752]
	adc edx, DWORD PTR [esi+1756]
	mov DWORD PTR [esi+1752], eax
	mov DWORD PTR [esi+1756], edx
	mov eax, DWORD PTR [esi+1720]
	mov edx, DWORD PTR [esi+1724]
	xor eax, DWORD PTR [esi+1752]
	xor edx, DWORD PTR [esi+1756]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1720], edx
	mov DWORD PTR [esi+1724], eax
	mov edx, DWORD PTR [esi+1720]
	mov eax, DWORD PTR [esi+1688]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1720]
	adc edx, DWORD PTR [esi+1724]
	add eax, DWORD PTR [esi+1688]
	adc edx, DWORD PTR [esi+1692]
	mov DWORD PTR [esi+1688], eax
	mov DWORD PTR [esi+1692], edx
	mov eax, DWORD PTR [esi+1784]
	mov edx, DWORD PTR [esi+1788]
	xor eax, DWORD PTR [esi+1688]
	xor edx, DWORD PTR [esi+1692]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1784], edx
	mov DWORD PTR [esi+1788], eax
	mov edx, DWORD PTR [esi+1784]
	mov eax, DWORD PTR [esi+1752]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1784]
	adc edx, DWORD PTR [esi+1788]
	add eax, DWORD PTR [esi+1752]
	adc edx, DWORD PTR [esi+1756]
	mov DWORD PTR [esi+1752], eax
	mov DWORD PTR [esi+1756], edx
	mov eax, DWORD PTR [esi+1720]
	mov edx, DWORD PTR [esi+1724]
	xor eax, DWORD PTR [esi+1752]
	xor edx, DWORD PTR [esi+1756]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1720], eax
	mov DWORD PTR [esi+1724], edx
	mov edx, DWORD PTR [esi+1704]
	mov eax, DWORD PTR [esi+1664]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1704]
	adc edx, DWORD PTR [esi+1708]
	add eax, DWORD PTR [esi+1664]
	adc edx, DWORD PTR [esi+1668]
	mov DWORD PTR [esi+1664], eax
	mov DWORD PTR [esi+1668], edx
	mov eax, DWORD PTR [esi+1784]
	mov edx, DWORD PTR [esi+1788]
	xor eax, DWORD PTR [esi+1664]
	xor edx, DWORD PTR [esi+1668]
	mov DWORD PTR [esi+1784], edx
	mov DWORD PTR [esi+1788], eax
	mov edx, DWORD PTR [esi+1784]
	mov eax, DWORD PTR [esi+1744]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1784]
	adc edx, DWORD PTR [esi+1788]
	add eax, DWORD PTR [esi+1744]
	adc edx, DWORD PTR [esi+1748]
	mov DWORD PTR [esi+1744], eax
	mov DWORD PTR [esi+1748], edx
	mov eax, DWORD PTR [esi+1704]
	mov edx, DWORD PTR [esi+1708]
	xor eax, DWORD PTR [esi+1744]
	xor edx, DWORD PTR [esi+1748]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1704], edx
	mov DWORD PTR [esi+1708], eax
	mov edx, DWORD PTR [esi+1704]
	mov eax, DWORD PTR [esi+1664]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1704]
	adc edx, DWORD PTR [esi+1708]
	add eax, DWORD PTR [esi+1664]
	adc edx, DWORD PTR [esi+1668]
	mov DWORD PTR [esi+1664], eax
	mov DWORD PTR [esi+1668], edx
	mov eax, DWORD PTR [esi+1784]
	mov edx, DWORD PTR [esi+1788]
	xor eax, DWORD PTR [esi+1664]
	xor edx, DWORD PTR [esi+1668]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1784], edx
	mov DWORD PTR [esi+1788], eax
	mov edx, DWORD PTR [esi+1784]
	mov eax, DWORD PTR [esi+1744]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1784]
	adc edx, DWORD PTR [esi+1788]
	add eax, DWORD PTR [esi+1744]
	adc edx, DWORD PTR [esi+1748]
	mov DWORD PTR [esi+1744], eax
	mov DWORD PTR [esi+1748], edx
	mov eax, DWORD PTR [esi+1704]
	mov edx, DWORD PTR [esi+1708]
	xor eax, DWORD PTR [esi+1744]
	xor edx, DWORD PTR [esi+1748]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1704], eax
	mov DWORD PTR [esi+1708], edx
	mov edx, DWORD PTR [esi+1712]
	mov eax, DWORD PTR [esi+1672]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1712]
	adc edx, DWORD PTR [esi+1716]
	add eax, DWORD PTR [esi+1672]
	adc edx, DWORD PTR [esi+1676]
	mov DWORD PTR [esi+1672], eax
	mov DWORD PTR [esi+1676], edx
	mov eax, DWORD PTR [esi+1760]
	mov edx, DWORD PTR [esi+1764]
	xor eax, DWORD PTR [esi+1672]
	xor edx, DWORD PTR [esi+1676]
	mov DWORD PTR [esi+1760], edx
	mov DWORD PTR [esi+1764], eax
	mov edx, DWORD PTR [esi+1760]
	mov eax, DWORD PTR [esi+1752]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1760]
	adc edx, DWORD PTR [esi+1764]
	add eax, DWORD PTR [esi+1752]
	adc edx, DWORD PTR [esi+1756]
	mov DWORD PTR [esi+1752], eax
	mov DWORD PTR [esi+1756], edx
	mov eax, DWORD PTR [esi+1712]
	mov edx, DWORD PTR [esi+1716]
	xor eax, DWORD PTR [esi+1752]
	xor edx, DWORD PTR [esi+1756]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1712], edx
	mov DWORD PTR [esi+1716], eax
	mov edx, DWORD PTR [esi+1712]
	mov eax, DWORD PTR [esi+1672]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1712]
	adc edx, DWORD PTR [esi+1716]
	add eax, DWORD PTR [esi+1672]
	adc edx, DWORD PTR [esi+1676]
	mov DWORD PTR [esi+1672], eax
	mov DWORD PTR [esi+1676], edx
	mov eax, DWORD PTR [esi+1760]
	mov edx, DWORD PTR [esi+1764]
	xor eax, DWORD PTR [esi+1672]
	xor edx, DWORD PTR [esi+1676]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1760], edx
	mov DWORD PTR [esi+1764], eax
	mov edx, DWORD PTR [esi+1760]
	mov eax, DWORD PTR [esi+1752]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1760]
	adc edx, DWORD PTR [esi+1764]
	add eax, DWORD PTR [esi+1752]
	adc edx, DWORD PTR [esi+1756]
	mov DWORD PTR [esi+1752], eax
	mov DWORD PTR [esi+1756], edx
	mov eax, DWORD PTR [esi+1712]
	mov edx, DWORD PTR [esi+1716]
	xor eax, DWORD PTR [esi+1752]
	xor edx, DWORD PTR [esi+1756]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1712], eax
	mov DWORD PTR [esi+1716], edx
	mov edx, DWORD PTR [esi+1720]
	mov eax, DWORD PTR [esi+1680]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1720]
	adc edx, DWORD PTR [esi+1724]
	add eax, DWORD PTR [esi+1680]
	adc edx, DWORD PTR [esi+1684]
	mov DWORD PTR [esi+1680], eax
	mov DWORD PTR [esi+1684], edx
	mov eax, DWORD PTR [esi+1768]
	mov edx, DWORD PTR [esi+1772]
	xor eax, DWORD PTR [esi+1680]
	xor edx, DWORD PTR [esi+1684]
	mov DWORD PTR [esi+1768], edx
	mov DWORD PTR [esi+1772], eax
	mov edx, DWORD PTR [esi+1768]
	mov eax, DWORD PTR [esi+1728]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1768]
	adc edx, DWORD PTR [esi+1772]
	add eax, DWORD PTR [esi+1728]
	adc edx, DWORD PTR [esi+1732]
	mov DWORD PTR [esi+1728], eax
	mov DWORD PTR [esi+1732], edx
	mov eax, DWORD PTR [esi+1720]
	mov edx, DWORD PTR [esi+1724]
	xor eax, DWORD PTR [esi+1728]
	xor edx, DWORD PTR [esi+1732]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1720], edx
	mov DWORD PTR [esi+1724], eax
	mov edx, DWORD PTR [esi+1720]
	mov eax, DWORD PTR [esi+1680]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1720]
	adc edx, DWORD PTR [esi+1724]
	add eax, DWORD PTR [esi+1680]
	adc edx, DWORD PTR [esi+1684]
	mov DWORD PTR [esi+1680], eax
	mov DWORD PTR [esi+1684], edx
	mov eax, DWORD PTR [esi+1768]
	mov edx, DWORD PTR [esi+1772]
	xor eax, DWORD PTR [esi+1680]
	xor edx, DWORD PTR [esi+1684]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1768], edx
	mov DWORD PTR [esi+1772], eax
	mov edx, DWORD PTR [esi+1768]
	mov eax, DWORD PTR [esi+1728]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1768]
	adc edx, DWORD PTR [esi+1772]
	add eax, DWORD PTR [esi+1728]
	adc edx, DWORD PTR [esi+1732]
	mov DWORD PTR [esi+1728], eax
	mov DWORD PTR [esi+1732], edx
	mov eax, DWORD PTR [esi+1720]
	mov edx, DWORD PTR [esi+1724]
	xor eax, DWORD PTR [esi+1728]
	xor edx, DWORD PTR [esi+1732]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1720], eax
	mov DWORD PTR [esi+1724], edx
	mov edx, DWORD PTR [esi+1696]
	mov eax, DWORD PTR [esi+1688]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1696]
	adc edx, DWORD PTR [esi+1700]
	add eax, DWORD PTR [esi+1688]
	adc edx, DWORD PTR [esi+1692]
	mov DWORD PTR [esi+1688], eax
	mov DWORD PTR [esi+1692], edx
	mov eax, DWORD PTR [esi+1776]
	mov edx, DWORD PTR [esi+1780]
	xor eax, DWORD PTR [esi+1688]
	xor edx, DWORD PTR [esi+1692]
	mov DWORD PTR [esi+1776], edx
	mov DWORD PTR [esi+1780], eax
	mov edx, DWORD PTR [esi+1776]
	mov eax, DWORD PTR [esi+1736]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1776]
	adc edx, DWORD PTR [esi+1780]
	add eax, DWORD PTR [esi+1736]
	adc edx, DWORD PTR [esi+1740]
	mov DWORD PTR [esi+1736], eax
	mov DWORD PTR [esi+1740], edx
	mov eax, DWORD PTR [esi+1696]
	mov edx, DWORD PTR [esi+1700]
	xor eax, DWORD PTR [esi+1736]
	xor edx, DWORD PTR [esi+1740]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1696], edx
	mov DWORD PTR [esi+1700], eax
	mov edx, DWORD PTR [esi+1696]
	mov eax, DWORD PTR [esi+1688]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1696]
	adc edx, DWORD PTR [esi+1700]
	add eax, DWORD PTR [esi+1688]
	adc edx, DWORD PTR [esi+1692]
	mov DWORD PTR [esi+1688], eax
	mov DWORD PTR [esi+1692], edx
	mov eax, DWORD PTR [esi+1776]
	mov edx, DWORD PTR [esi+1780]
	xor eax, DWORD PTR [esi+1688]
	xor edx, DWORD PTR [esi+1692]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1776], edx
	mov DWORD PTR [esi+1780], eax
	mov edx, DWORD PTR [esi+1776]
	mov eax, DWORD PTR [esi+1736]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1776]
	adc edx, DWORD PTR [esi+1780]
	add eax, DWORD PTR [esi+1736]
	adc edx, DWORD PTR [esi+1740]
	mov DWORD PTR [esi+1736], eax
	mov DWORD PTR [esi+1740], edx
	mov eax, DWORD PTR [esi+1696]
	mov edx, DWORD PTR [esi+1700]
	xor eax, DWORD PTR [esi+1736]
	xor edx, DWORD PTR [esi+1740]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1696], eax
	mov DWORD PTR [esi+1700], edx
	mov edx, DWORD PTR [esi+1824]
	mov eax, DWORD PTR [esi+1792]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1824]
	adc edx, DWORD PTR [esi+1828]
	add eax, DWORD PTR [esi+1792]
	adc edx, DWORD PTR [esi+1796]
	mov DWORD PTR [esi+1792], eax
	mov DWORD PTR [esi+1796], edx
	mov eax, DWORD PTR [esi+1888]
	mov edx, DWORD PTR [esi+1892]
	xor eax, DWORD PTR [esi+1792]
	xor edx, DWORD PTR [esi+1796]
	mov DWORD PTR [esi+1888], edx
	mov DWORD PTR [esi+1892], eax
	mov edx, DWORD PTR [esi+1888]
	mov eax, DWORD PTR [esi+1856]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1888]
	adc edx, DWORD PTR [esi+1892]
	add eax, DWORD PTR [esi+1856]
	adc edx, DWORD PTR [esi+1860]
	mov DWORD PTR [esi+1856], eax
	mov DWORD PTR [esi+1860], edx
	mov eax, DWORD PTR [esi+1824]
	mov edx, DWORD PTR [esi+1828]
	xor eax, DWORD PTR [esi+1856]
	xor edx, DWORD PTR [esi+1860]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1824], edx
	mov DWORD PTR [esi+1828], eax
	mov edx, DWORD PTR [esi+1824]
	mov eax, DWORD PTR [esi+1792]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1824]
	adc edx, DWORD PTR [esi+1828]
	add eax, DWORD PTR [esi+1792]
	adc edx, DWORD PTR [esi+1796]
	mov DWORD PTR [esi+1792], eax
	mov DWORD PTR [esi+1796], edx
	mov eax, DWORD PTR [esi+1888]
	mov edx, DWORD PTR [esi+1892]
	xor eax, DWORD PTR [esi+1792]
	xor edx, DWORD PTR [esi+1796]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1888], edx
	mov DWORD PTR [esi+1892], eax
	mov edx, DWORD PTR [esi+1888]
	mov eax, DWORD PTR [esi+1856]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1888]
	adc edx, DWORD PTR [esi+1892]
	add eax, DWORD PTR [esi+1856]
	adc edx, DWORD PTR [esi+1860]
	mov DWORD PTR [esi+1856], eax
	mov DWORD PTR [esi+1860], edx
	mov eax, DWORD PTR [esi+1824]
	mov edx, DWORD PTR [esi+1828]
	xor eax, DWORD PTR [esi+1856]
	xor edx, DWORD PTR [esi+1860]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1824], eax
	mov DWORD PTR [esi+1828], edx
	mov edx, DWORD PTR [esi+1832]
	mov eax, DWORD PTR [esi+1800]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1832]
	adc edx, DWORD PTR [esi+1836]
	add eax, DWORD PTR [esi+1800]
	adc edx, DWORD PTR [esi+1804]
	mov DWORD PTR [esi+1800], eax
	mov DWORD PTR [esi+1804], edx
	mov eax, DWORD PTR [esi+1896]
	mov edx, DWORD PTR [esi+1900]
	xor eax, DWORD PTR [esi+1800]
	xor edx, DWORD PTR [esi+1804]
	mov DWORD PTR [esi+1896], edx
	mov DWORD PTR [esi+1900], eax
	mov edx, DWORD PTR [esi+1896]
	mov eax, DWORD PTR [esi+1864]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1896]
	adc edx, DWORD PTR [esi+1900]
	add eax, DWORD PTR [esi+1864]
	adc edx, DWORD PTR [esi+1868]
	mov DWORD PTR [esi+1864], eax
	mov DWORD PTR [esi+1868], edx
	mov eax, DWORD PTR [esi+1832]
	mov edx, DWORD PTR [esi+1836]
	xor eax, DWORD PTR [esi+1864]
	xor edx, DWORD PTR [esi+1868]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1832], edx
	mov DWORD PTR [esi+1836], eax
	mov edx, DWORD PTR [esi+1832]
	mov eax, DWORD PTR [esi+1800]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1832]
	adc edx, DWORD PTR [esi+1836]
	add eax, DWORD PTR [esi+1800]
	adc edx, DWORD PTR [esi+1804]
	mov DWORD PTR [esi+1800], eax
	mov DWORD PTR [esi+1804], edx
	mov eax, DWORD PTR [esi+1896]
	mov edx, DWORD PTR [esi+1900]
	xor eax, DWORD PTR [esi+1800]
	xor edx, DWORD PTR [esi+1804]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1896], edx
	mov DWORD PTR [esi+1900], eax
	mov edx, DWORD PTR [esi+1896]
	mov eax, DWORD PTR [esi+1864]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1896]
	adc edx, DWORD PTR [esi+1900]
	add eax, DWORD PTR [esi+1864]
	adc edx, DWORD PTR [esi+1868]
	mov DWORD PTR [esi+1864], eax
	mov DWORD PTR [esi+1868], edx
	mov eax, DWORD PTR [esi+1832]
	mov edx, DWORD PTR [esi+1836]
	xor eax, DWORD PTR [esi+1864]
	xor edx, DWORD PTR [esi+1868]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1832], eax
	mov DWORD PTR [esi+1836], edx
	mov edx, DWORD PTR [esi+1840]
	mov eax, DWORD PTR [esi+1808]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1840]
	adc edx, DWORD PTR [esi+1844]
	add eax, DWORD PTR [esi+1808]
	adc edx, DWORD PTR [esi+1812]
	mov DWORD PTR [esi+1808], eax
	mov DWORD PTR [esi+1812], edx
	mov eax, DWORD PTR [esi+1904]
	mov edx, DWORD PTR [esi+1908]
	xor eax, DWORD PTR [esi+1808]
	xor edx, DWORD PTR [esi+1812]
	mov DWORD PTR [esi+1904], edx
	mov DWORD PTR [esi+1908], eax
	mov edx, DWORD PTR [esi+1904]
	mov eax, DWORD PTR [esi+1872]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1904]
	adc edx, DWORD PTR [esi+1908]
	add eax, DWORD PTR [esi+1872]
	adc edx, DWORD PTR [esi+1876]
	mov DWORD PTR [esi+1872], eax
	mov DWORD PTR [esi+1876], edx
	mov eax, DWORD PTR [esi+1840]
	mov edx, DWORD PTR [esi+1844]
	xor eax, DWORD PTR [esi+1872]
	xor edx, DWORD PTR [esi+1876]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1840], edx
	mov DWORD PTR [esi+1844], eax
	mov edx, DWORD PTR [esi+1840]
	mov eax, DWORD PTR [esi+1808]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1840]
	adc edx, DWORD PTR [esi+1844]
	add eax, DWORD PTR [esi+1808]
	adc edx, DWORD PTR [esi+1812]
	mov DWORD PTR [esi+1808], eax
	mov DWORD PTR [esi+1812], edx
	mov eax, DWORD PTR [esi+1904]
	mov edx, DWORD PTR [esi+1908]
	xor eax, DWORD PTR [esi+1808]
	xor edx, DWORD PTR [esi+1812]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1904], edx
	mov DWORD PTR [esi+1908], eax
	mov edx, DWORD PTR [esi+1904]
	mov eax, DWORD PTR [esi+1872]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1904]
	adc edx, DWORD PTR [esi+1908]
	add eax, DWORD PTR [esi+1872]
	adc edx, DWORD PTR [esi+1876]
	mov DWORD PTR [esi+1872], eax
	mov DWORD PTR [esi+1876], edx
	mov eax, DWORD PTR [esi+1840]
	mov edx, DWORD PTR [esi+1844]
	xor eax, DWORD PTR [esi+1872]
	xor edx, DWORD PTR [esi+1876]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1840], eax
	mov DWORD PTR [esi+1844], edx
	mov edx, DWORD PTR [esi+1848]
	mov eax, DWORD PTR [esi+1816]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1848]
	adc edx, DWORD PTR [esi+1852]
	add eax, DWORD PTR [esi+1816]
	adc edx, DWORD PTR [esi+1820]
	mov DWORD PTR [esi+1816], eax
	mov DWORD PTR [esi+1820], edx
	mov eax, DWORD PTR [esi+1912]
	mov edx, DWORD PTR [esi+1916]
	xor eax, DWORD PTR [esi+1816]
	xor edx, DWORD PTR [esi+1820]
	mov DWORD PTR [esi+1912], edx
	mov DWORD PTR [esi+1916], eax
	mov edx, DWORD PTR [esi+1912]
	mov eax, DWORD PTR [esi+1880]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1912]
	adc edx, DWORD PTR [esi+1916]
	add eax, DWORD PTR [esi+1880]
	adc edx, DWORD PTR [esi+1884]
	mov DWORD PTR [esi+1880], eax
	mov DWORD PTR [esi+1884], edx
	mov eax, DWORD PTR [esi+1848]
	mov edx, DWORD PTR [esi+1852]
	xor eax, DWORD PTR [esi+1880]
	xor edx, DWORD PTR [esi+1884]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1848], edx
	mov DWORD PTR [esi+1852], eax
	mov edx, DWORD PTR [esi+1848]
	mov eax, DWORD PTR [esi+1816]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1848]
	adc edx, DWORD PTR [esi+1852]
	add eax, DWORD PTR [esi+1816]
	adc edx, DWORD PTR [esi+1820]
	mov DWORD PTR [esi+1816], eax
	mov DWORD PTR [esi+1820], edx
	mov eax, DWORD PTR [esi+1912]
	mov edx, DWORD PTR [esi+1916]
	xor eax, DWORD PTR [esi+1816]
	xor edx, DWORD PTR [esi+1820]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1912], edx
	mov DWORD PTR [esi+1916], eax
	mov edx, DWORD PTR [esi+1912]
	mov eax, DWORD PTR [esi+1880]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1912]
	adc edx, DWORD PTR [esi+1916]
	add eax, DWORD PTR [esi+1880]
	adc edx, DWORD PTR [esi+1884]
	mov DWORD PTR [esi+1880], eax
	mov DWORD PTR [esi+1884], edx
	mov eax, DWORD PTR [esi+1848]
	mov edx, DWORD PTR [esi+1852]
	xor eax, DWORD PTR [esi+1880]
	xor edx, DWORD PTR [esi+1884]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1848], eax
	mov DWORD PTR [esi+1852], edx
	mov edx, DWORD PTR [esi+1832]
	mov eax, DWORD PTR [esi+1792]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1832]
	adc edx, DWORD PTR [esi+1836]
	add eax, DWORD PTR [esi+1792]
	adc edx, DWORD PTR [esi+1796]
	mov DWORD PTR [esi+1792], eax
	mov DWORD PTR [esi+1796], edx
	mov eax, DWORD PTR [esi+1912]
	mov edx, DWORD PTR [esi+1916]
	xor eax, DWORD PTR [esi+1792]
	xor edx, DWORD PTR [esi+1796]
	mov DWORD PTR [esi+1912], edx
	mov DWORD PTR [esi+1916], eax
	mov edx, DWORD PTR [esi+1912]
	mov eax, DWORD PTR [esi+1872]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1912]
	adc edx, DWORD PTR [esi+1916]
	add eax, DWORD PTR [esi+1872]
	adc edx, DWORD PTR [esi+1876]
	mov DWORD PTR [esi+1872], eax
	mov DWORD PTR [esi+1876], edx
	mov eax, DWORD PTR [esi+1832]
	mov edx, DWORD PTR [esi+1836]
	xor eax, DWORD PTR [esi+1872]
	xor edx, DWORD PTR [esi+1876]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1832], edx
	mov DWORD PTR [esi+1836], eax
	mov edx, DWORD PTR [esi+1832]
	mov eax, DWORD PTR [esi+1792]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1832]
	adc edx, DWORD PTR [esi+1836]
	add eax, DWORD PTR [esi+1792]
	adc edx, DWORD PTR [esi+1796]
	mov DWORD PTR [esi+1792], eax
	mov DWORD PTR [esi+1796], edx
	mov eax, DWORD PTR [esi+1912]
	mov edx, DWORD PTR [esi+1916]
	xor eax, DWORD PTR [esi+1792]
	xor edx, DWORD PTR [esi+1796]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1912], edx
	mov DWORD PTR [esi+1916], eax
	mov edx, DWORD PTR [esi+1912]
	mov eax, DWORD PTR [esi+1872]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1912]
	adc edx, DWORD PTR [esi+1916]
	add eax, DWORD PTR [esi+1872]
	adc edx, DWORD PTR [esi+1876]
	mov DWORD PTR [esi+1872], eax
	mov DWORD PTR [esi+1876], edx
	mov eax, DWORD PTR [esi+1832]
	mov edx, DWORD PTR [esi+1836]
	xor eax, DWORD PTR [esi+1872]
	xor edx, DWORD PTR [esi+1876]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1832], eax
	mov DWORD PTR [esi+1836], edx
	mov edx, DWORD PTR [esi+1840]
	mov eax, DWORD PTR [esi+1800]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1840]
	adc edx, DWORD PTR [esi+1844]
	add eax, DWORD PTR [esi+1800]
	adc edx, DWORD PTR [esi+1804]
	mov DWORD PTR [esi+1800], eax
	mov DWORD PTR [esi+1804], edx
	mov eax, DWORD PTR [esi+1888]
	mov edx, DWORD PTR [esi+1892]
	xor eax, DWORD PTR [esi+1800]
	xor edx, DWORD PTR [esi+1804]
	mov DWORD PTR [esi+1888], edx
	mov DWORD PTR [esi+1892], eax
	mov edx, DWORD PTR [esi+1888]
	mov eax, DWORD PTR [esi+1880]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1888]
	adc edx, DWORD PTR [esi+1892]
	add eax, DWORD PTR [esi+1880]
	adc edx, DWORD PTR [esi+1884]
	mov DWORD PTR [esi+1880], eax
	mov DWORD PTR [esi+1884], edx
	mov eax, DWORD PTR [esi+1840]
	mov edx, DWORD PTR [esi+1844]
	xor eax, DWORD PTR [esi+1880]
	xor edx, DWORD PTR [esi+1884]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1840], edx
	mov DWORD PTR [esi+1844], eax
	mov edx, DWORD PTR [esi+1840]
	mov eax, DWORD PTR [esi+1800]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1840]
	adc edx, DWORD PTR [esi+1844]
	add eax, DWORD PTR [esi+1800]
	adc edx, DWORD PTR [esi+1804]
	mov DWORD PTR [esi+1800], eax
	mov DWORD PTR [esi+1804], edx
	mov eax, DWORD PTR [esi+1888]
	mov edx, DWORD PTR [esi+1892]
	xor eax, DWORD PTR [esi+1800]
	xor edx, DWORD PTR [esi+1804]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1888], edx
	mov DWORD PTR [esi+1892], eax
	mov edx, DWORD PTR [esi+1888]
	mov eax, DWORD PTR [esi+1880]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1888]
	adc edx, DWORD PTR [esi+1892]
	add eax, DWORD PTR [esi+1880]
	adc edx, DWORD PTR [esi+1884]
	mov DWORD PTR [esi+1880], eax
	mov DWORD PTR [esi+1884], edx
	mov eax, DWORD PTR [esi+1840]
	mov edx, DWORD PTR [esi+1844]
	xor eax, DWORD PTR [esi+1880]
	xor edx, DWORD PTR [esi+1884]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1840], eax
	mov DWORD PTR [esi+1844], edx
	mov edx, DWORD PTR [esi+1848]
	mov eax, DWORD PTR [esi+1808]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1848]
	adc edx, DWORD PTR [esi+1852]
	add eax, DWORD PTR [esi+1808]
	adc edx, DWORD PTR [esi+1812]
	mov DWORD PTR [esi+1808], eax
	mov DWORD PTR [esi+1812], edx
	mov eax, DWORD PTR [esi+1896]
	mov edx, DWORD PTR [esi+1900]
	xor eax, DWORD PTR [esi+1808]
	xor edx, DWORD PTR [esi+1812]
	mov DWORD PTR [esi+1896], edx
	mov DWORD PTR [esi+1900], eax
	mov edx, DWORD PTR [esi+1896]
	mov eax, DWORD PTR [esi+1856]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1896]
	adc edx, DWORD PTR [esi+1900]
	add eax, DWORD PTR [esi+1856]
	adc edx, DWORD PTR [esi+1860]
	mov DWORD PTR [esi+1856], eax
	mov DWORD PTR [esi+1860], edx
	mov eax, DWORD PTR [esi+1848]
	mov edx, DWORD PTR [esi+1852]
	xor eax, DWORD PTR [esi+1856]
	xor edx, DWORD PTR [esi+1860]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1848], edx
	mov DWORD PTR [esi+1852], eax
	mov edx, DWORD PTR [esi+1848]
	mov eax, DWORD PTR [esi+1808]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1848]
	adc edx, DWORD PTR [esi+1852]
	add eax, DWORD PTR [esi+1808]
	adc edx, DWORD PTR [esi+1812]
	mov DWORD PTR [esi+1808], eax
	mov DWORD PTR [esi+1812], edx
	mov eax, DWORD PTR [esi+1896]
	mov edx, DWORD PTR [esi+1900]
	xor eax, DWORD PTR [esi+1808]
	xor edx, DWORD PTR [esi+1812]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1896], edx
	mov DWORD PTR [esi+1900], eax
	mov edx, DWORD PTR [esi+1896]
	mov eax, DWORD PTR [esi+1856]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1896]
	adc edx, DWORD PTR [esi+1900]
	add eax, DWORD PTR [esi+1856]
	adc edx, DWORD PTR [esi+1860]
	mov DWORD PTR [esi+1856], eax
	mov DWORD PTR [esi+1860], edx
	mov eax, DWORD PTR [esi+1848]
	mov edx, DWORD PTR [esi+1852]
	xor eax, DWORD PTR [esi+1856]
	xor edx, DWORD PTR [esi+1860]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1848], eax
	mov DWORD PTR [esi+1852], edx
	mov edx, DWORD PTR [esi+1824]
	mov eax, DWORD PTR [esi+1816]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1824]
	adc edx, DWORD PTR [esi+1828]
	add eax, DWORD PTR [esi+1816]
	adc edx, DWORD PTR [esi+1820]
	mov DWORD PTR [esi+1816], eax
	mov DWORD PTR [esi+1820], edx
	mov eax, DWORD PTR [esi+1904]
	mov edx, DWORD PTR [esi+1908]
	xor eax, DWORD PTR [esi+1816]
	xor edx, DWORD PTR [esi+1820]
	mov DWORD PTR [esi+1904], edx
	mov DWORD PTR [esi+1908], eax
	mov edx, DWORD PTR [esi+1904]
	mov eax, DWORD PTR [esi+1864]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1904]
	adc edx, DWORD PTR [esi+1908]
	add eax, DWORD PTR [esi+1864]
	adc edx, DWORD PTR [esi+1868]
	mov DWORD PTR [esi+1864], eax
	mov DWORD PTR [esi+1868], edx
	mov eax, DWORD PTR [esi+1824]
	mov edx, DWORD PTR [esi+1828]
	xor eax, DWORD PTR [esi+1864]
	xor edx, DWORD PTR [esi+1868]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1824], edx
	mov DWORD PTR [esi+1828], eax
	mov edx, DWORD PTR [esi+1824]
	mov eax, DWORD PTR [esi+1816]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1824]
	adc edx, DWORD PTR [esi+1828]
	add eax, DWORD PTR [esi+1816]
	adc edx, DWORD PTR [esi+1820]
	mov DWORD PTR [esi+1816], eax
	mov DWORD PTR [esi+1820], edx
	mov eax, DWORD PTR [esi+1904]
	mov edx, DWORD PTR [esi+1908]
	xor eax, DWORD PTR [esi+1816]
	xor edx, DWORD PTR [esi+1820]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1904], edx
	mov DWORD PTR [esi+1908], eax
	mov edx, DWORD PTR [esi+1904]
	mov eax, DWORD PTR [esi+1864]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1904]
	adc edx, DWORD PTR [esi+1908]
	add eax, DWORD PTR [esi+1864]
	adc edx, DWORD PTR [esi+1868]
	mov DWORD PTR [esi+1864], eax
	mov DWORD PTR [esi+1868], edx
	mov eax, DWORD PTR [esi+1824]
	mov edx, DWORD PTR [esi+1828]
	xor eax, DWORD PTR [esi+1864]
	xor edx, DWORD PTR [esi+1868]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1824], eax
	mov DWORD PTR [esi+1828], edx
	mov edx, DWORD PTR [esi+1952]
	mov eax, DWORD PTR [esi+1920]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1952]
	adc edx, DWORD PTR [esi+1956]
	add eax, DWORD PTR [esi+1920]
	adc edx, DWORD PTR [esi+1924]
	mov DWORD PTR [esi+1920], eax
	mov DWORD PTR [esi+1924], edx
	mov eax, DWORD PTR [esi+2016]
	mov edx, DWORD PTR [esi+2020]
	xor eax, DWORD PTR [esi+1920]
	xor edx, DWORD PTR [esi+1924]
	mov DWORD PTR [esi+2016], edx
	mov DWORD PTR [esi+2020], eax
	mov edx, DWORD PTR [esi+2016]
	mov eax, DWORD PTR [esi+1984]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2016]
	adc edx, DWORD PTR [esi+2020]
	add eax, DWORD PTR [esi+1984]
	adc edx, DWORD PTR [esi+1988]
	mov DWORD PTR [esi+1984], eax
	mov DWORD PTR [esi+1988], edx
	mov eax, DWORD PTR [esi+1952]
	mov edx, DWORD PTR [esi+1956]
	xor eax, DWORD PTR [esi+1984]
	xor edx, DWORD PTR [esi+1988]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1952], edx
	mov DWORD PTR [esi+1956], eax
	mov edx, DWORD PTR [esi+1952]
	mov eax, DWORD PTR [esi+1920]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1952]
	adc edx, DWORD PTR [esi+1956]
	add eax, DWORD PTR [esi+1920]
	adc edx, DWORD PTR [esi+1924]
	mov DWORD PTR [esi+1920], eax
	mov DWORD PTR [esi+1924], edx
	mov eax, DWORD PTR [esi+2016]
	mov edx, DWORD PTR [esi+2020]
	xor eax, DWORD PTR [esi+1920]
	xor edx, DWORD PTR [esi+1924]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2016], edx
	mov DWORD PTR [esi+2020], eax
	mov edx, DWORD PTR [esi+2016]
	mov eax, DWORD PTR [esi+1984]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2016]
	adc edx, DWORD PTR [esi+2020]
	add eax, DWORD PTR [esi+1984]
	adc edx, DWORD PTR [esi+1988]
	mov DWORD PTR [esi+1984], eax
	mov DWORD PTR [esi+1988], edx
	mov eax, DWORD PTR [esi+1952]
	mov edx, DWORD PTR [esi+1956]
	xor eax, DWORD PTR [esi+1984]
	xor edx, DWORD PTR [esi+1988]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1952], eax
	mov DWORD PTR [esi+1956], edx
	mov edx, DWORD PTR [esi+1960]
	mov eax, DWORD PTR [esi+1928]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1960]
	adc edx, DWORD PTR [esi+1964]
	add eax, DWORD PTR [esi+1928]
	adc edx, DWORD PTR [esi+1932]
	mov DWORD PTR [esi+1928], eax
	mov DWORD PTR [esi+1932], edx
	mov eax, DWORD PTR [esi+2024]
	mov edx, DWORD PTR [esi+2028]
	xor eax, DWORD PTR [esi+1928]
	xor edx, DWORD PTR [esi+1932]
	mov DWORD PTR [esi+2024], edx
	mov DWORD PTR [esi+2028], eax
	mov edx, DWORD PTR [esi+2024]
	mov eax, DWORD PTR [esi+1992]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2024]
	adc edx, DWORD PTR [esi+2028]
	add eax, DWORD PTR [esi+1992]
	adc edx, DWORD PTR [esi+1996]
	mov DWORD PTR [esi+1992], eax
	mov DWORD PTR [esi+1996], edx
	mov eax, DWORD PTR [esi+1960]
	mov edx, DWORD PTR [esi+1964]
	xor eax, DWORD PTR [esi+1992]
	xor edx, DWORD PTR [esi+1996]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1960], edx
	mov DWORD PTR [esi+1964], eax
	mov edx, DWORD PTR [esi+1960]
	mov eax, DWORD PTR [esi+1928]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1960]
	adc edx, DWORD PTR [esi+1964]
	add eax, DWORD PTR [esi+1928]
	adc edx, DWORD PTR [esi+1932]
	mov DWORD PTR [esi+1928], eax
	mov DWORD PTR [esi+1932], edx
	mov eax, DWORD PTR [esi+2024]
	mov edx, DWORD PTR [esi+2028]
	xor eax, DWORD PTR [esi+1928]
	xor edx, DWORD PTR [esi+1932]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2024], edx
	mov DWORD PTR [esi+2028], eax
	mov edx, DWORD PTR [esi+2024]
	mov eax, DWORD PTR [esi+1992]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2024]
	adc edx, DWORD PTR [esi+2028]
	add eax, DWORD PTR [esi+1992]
	adc edx, DWORD PTR [esi+1996]
	mov DWORD PTR [esi+1992], eax
	mov DWORD PTR [esi+1996], edx
	mov eax, DWORD PTR [esi+1960]
	mov edx, DWORD PTR [esi+1964]
	xor eax, DWORD PTR [esi+1992]
	xor edx, DWORD PTR [esi+1996]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1960], eax
	mov DWORD PTR [esi+1964], edx
	mov edx, DWORD PTR [esi+1968]
	mov eax, DWORD PTR [esi+1936]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1968]
	adc edx, DWORD PTR [esi+1972]
	add eax, DWORD PTR [esi+1936]
	adc edx, DWORD PTR [esi+1940]
	mov DWORD PTR [esi+1936], eax
	mov DWORD PTR [esi+1940], edx
	mov eax, DWORD PTR [esi+2032]
	mov edx, DWORD PTR [esi+2036]
	xor eax, DWORD PTR [esi+1936]
	xor edx, DWORD PTR [esi+1940]
	mov DWORD PTR [esi+2032], edx
	mov DWORD PTR [esi+2036], eax
	mov edx, DWORD PTR [esi+2032]
	mov eax, DWORD PTR [esi+2000]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2032]
	adc edx, DWORD PTR [esi+2036]
	add eax, DWORD PTR [esi+2000]
	adc edx, DWORD PTR [esi+2004]
	mov DWORD PTR [esi+2000], eax
	mov DWORD PTR [esi+2004], edx
	mov eax, DWORD PTR [esi+1968]
	mov edx, DWORD PTR [esi+1972]
	xor eax, DWORD PTR [esi+2000]
	xor edx, DWORD PTR [esi+2004]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1968], edx
	mov DWORD PTR [esi+1972], eax
	mov edx, DWORD PTR [esi+1968]
	mov eax, DWORD PTR [esi+1936]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1968]
	adc edx, DWORD PTR [esi+1972]
	add eax, DWORD PTR [esi+1936]
	adc edx, DWORD PTR [esi+1940]
	mov DWORD PTR [esi+1936], eax
	mov DWORD PTR [esi+1940], edx
	mov eax, DWORD PTR [esi+2032]
	mov edx, DWORD PTR [esi+2036]
	xor eax, DWORD PTR [esi+1936]
	xor edx, DWORD PTR [esi+1940]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2032], edx
	mov DWORD PTR [esi+2036], eax
	mov edx, DWORD PTR [esi+2032]
	mov eax, DWORD PTR [esi+2000]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2032]
	adc edx, DWORD PTR [esi+2036]
	add eax, DWORD PTR [esi+2000]
	adc edx, DWORD PTR [esi+2004]
	mov DWORD PTR [esi+2000], eax
	mov DWORD PTR [esi+2004], edx
	mov eax, DWORD PTR [esi+1968]
	mov edx, DWORD PTR [esi+1972]
	xor eax, DWORD PTR [esi+2000]
	xor edx, DWORD PTR [esi+2004]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1968], eax
	mov DWORD PTR [esi+1972], edx
	mov edx, DWORD PTR [esi+1976]
	mov eax, DWORD PTR [esi+1944]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1976]
	adc edx, DWORD PTR [esi+1980]
	add eax, DWORD PTR [esi+1944]
	adc edx, DWORD PTR [esi+1948]
	mov DWORD PTR [esi+1944], eax
	mov DWORD PTR [esi+1948], edx
	mov eax, DWORD PTR [esi+2040]
	mov edx, DWORD PTR [esi+2044]
	xor eax, DWORD PTR [esi+1944]
	xor edx, DWORD PTR [esi+1948]
	mov DWORD PTR [esi+2040], edx
	mov DWORD PTR [esi+2044], eax
	mov edx, DWORD PTR [esi+2040]
	mov eax, DWORD PTR [esi+2008]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2040]
	adc edx, DWORD PTR [esi+2044]
	add eax, DWORD PTR [esi+2008]
	adc edx, DWORD PTR [esi+2012]
	mov DWORD PTR [esi+2008], eax
	mov DWORD PTR [esi+2012], edx
	mov eax, DWORD PTR [esi+1976]
	mov edx, DWORD PTR [esi+1980]
	xor eax, DWORD PTR [esi+2008]
	xor edx, DWORD PTR [esi+2012]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1976], edx
	mov DWORD PTR [esi+1980], eax
	mov edx, DWORD PTR [esi+1976]
	mov eax, DWORD PTR [esi+1944]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1976]
	adc edx, DWORD PTR [esi+1980]
	add eax, DWORD PTR [esi+1944]
	adc edx, DWORD PTR [esi+1948]
	mov DWORD PTR [esi+1944], eax
	mov DWORD PTR [esi+1948], edx
	mov eax, DWORD PTR [esi+2040]
	mov edx, DWORD PTR [esi+2044]
	xor eax, DWORD PTR [esi+1944]
	xor edx, DWORD PTR [esi+1948]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2040], edx
	mov DWORD PTR [esi+2044], eax
	mov edx, DWORD PTR [esi+2040]
	mov eax, DWORD PTR [esi+2008]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2040]
	adc edx, DWORD PTR [esi+2044]
	add eax, DWORD PTR [esi+2008]
	adc edx, DWORD PTR [esi+2012]
	mov DWORD PTR [esi+2008], eax
	mov DWORD PTR [esi+2012], edx
	mov eax, DWORD PTR [esi+1976]
	mov edx, DWORD PTR [esi+1980]
	xor eax, DWORD PTR [esi+2008]
	xor edx, DWORD PTR [esi+2012]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1976], eax
	mov DWORD PTR [esi+1980], edx
	mov edx, DWORD PTR [esi+1960]
	mov eax, DWORD PTR [esi+1920]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1960]
	adc edx, DWORD PTR [esi+1964]
	add eax, DWORD PTR [esi+1920]
	adc edx, DWORD PTR [esi+1924]
	mov DWORD PTR [esi+1920], eax
	mov DWORD PTR [esi+1924], edx
	mov eax, DWORD PTR [esi+2040]
	mov edx, DWORD PTR [esi+2044]
	xor eax, DWORD PTR [esi+1920]
	xor edx, DWORD PTR [esi+1924]
	mov DWORD PTR [esi+2040], edx
	mov DWORD PTR [esi+2044], eax
	mov edx, DWORD PTR [esi+2040]
	mov eax, DWORD PTR [esi+2000]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2040]
	adc edx, DWORD PTR [esi+2044]
	add eax, DWORD PTR [esi+2000]
	adc edx, DWORD PTR [esi+2004]
	mov DWORD PTR [esi+2000], eax
	mov DWORD PTR [esi+2004], edx
	mov eax, DWORD PTR [esi+1960]
	mov edx, DWORD PTR [esi+1964]
	xor eax, DWORD PTR [esi+2000]
	xor edx, DWORD PTR [esi+2004]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1960], edx
	mov DWORD PTR [esi+1964], eax
	mov edx, DWORD PTR [esi+1960]
	mov eax, DWORD PTR [esi+1920]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1960]
	adc edx, DWORD PTR [esi+1964]
	add eax, DWORD PTR [esi+1920]
	adc edx, DWORD PTR [esi+1924]
	mov DWORD PTR [esi+1920], eax
	mov DWORD PTR [esi+1924], edx
	mov eax, DWORD PTR [esi+2040]
	mov edx, DWORD PTR [esi+2044]
	xor eax, DWORD PTR [esi+1920]
	xor edx, DWORD PTR [esi+1924]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2040], edx
	mov DWORD PTR [esi+2044], eax
	mov edx, DWORD PTR [esi+2040]
	mov eax, DWORD PTR [esi+2000]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2040]
	adc edx, DWORD PTR [esi+2044]
	add eax, DWORD PTR [esi+2000]
	adc edx, DWORD PTR [esi+2004]
	mov DWORD PTR [esi+2000], eax
	mov DWORD PTR [esi+2004], edx
	mov eax, DWORD PTR [esi+1960]
	mov edx, DWORD PTR [esi+1964]
	xor eax, DWORD PTR [esi+2000]
	xor edx, DWORD PTR [esi+2004]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1960], eax
	mov DWORD PTR [esi+1964], edx
	mov edx, DWORD PTR [esi+1968]
	mov eax, DWORD PTR [esi+1928]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1968]
	adc edx, DWORD PTR [esi+1972]
	add eax, DWORD PTR [esi+1928]
	adc edx, DWORD PTR [esi+1932]
	mov DWORD PTR [esi+1928], eax
	mov DWORD PTR [esi+1932], edx
	mov eax, DWORD PTR [esi+2016]
	mov edx, DWORD PTR [esi+2020]
	xor eax, DWORD PTR [esi+1928]
	xor edx, DWORD PTR [esi+1932]
	mov DWORD PTR [esi+2016], edx
	mov DWORD PTR [esi+2020], eax
	mov edx, DWORD PTR [esi+2016]
	mov eax, DWORD PTR [esi+2008]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2016]
	adc edx, DWORD PTR [esi+2020]
	add eax, DWORD PTR [esi+2008]
	adc edx, DWORD PTR [esi+2012]
	mov DWORD PTR [esi+2008], eax
	mov DWORD PTR [esi+2012], edx
	mov eax, DWORD PTR [esi+1968]
	mov edx, DWORD PTR [esi+1972]
	xor eax, DWORD PTR [esi+2008]
	xor edx, DWORD PTR [esi+2012]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1968], edx
	mov DWORD PTR [esi+1972], eax
	mov edx, DWORD PTR [esi+1968]
	mov eax, DWORD PTR [esi+1928]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1968]
	adc edx, DWORD PTR [esi+1972]
	add eax, DWORD PTR [esi+1928]
	adc edx, DWORD PTR [esi+1932]
	mov DWORD PTR [esi+1928], eax
	mov DWORD PTR [esi+1932], edx
	mov eax, DWORD PTR [esi+2016]
	mov edx, DWORD PTR [esi+2020]
	xor eax, DWORD PTR [esi+1928]
	xor edx, DWORD PTR [esi+1932]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2016], edx
	mov DWORD PTR [esi+2020], eax
	mov edx, DWORD PTR [esi+2016]
	mov eax, DWORD PTR [esi+2008]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2016]
	adc edx, DWORD PTR [esi+2020]
	add eax, DWORD PTR [esi+2008]
	adc edx, DWORD PTR [esi+2012]
	mov DWORD PTR [esi+2008], eax
	mov DWORD PTR [esi+2012], edx
	mov eax, DWORD PTR [esi+1968]
	mov edx, DWORD PTR [esi+1972]
	xor eax, DWORD PTR [esi+2008]
	xor edx, DWORD PTR [esi+2012]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1968], eax
	mov DWORD PTR [esi+1972], edx
	mov edx, DWORD PTR [esi+1976]
	mov eax, DWORD PTR [esi+1936]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1976]
	adc edx, DWORD PTR [esi+1980]
	add eax, DWORD PTR [esi+1936]
	adc edx, DWORD PTR [esi+1940]
	mov DWORD PTR [esi+1936], eax
	mov DWORD PTR [esi+1940], edx
	mov eax, DWORD PTR [esi+2024]
	mov edx, DWORD PTR [esi+2028]
	xor eax, DWORD PTR [esi+1936]
	xor edx, DWORD PTR [esi+1940]
	mov DWORD PTR [esi+2024], edx
	mov DWORD PTR [esi+2028], eax
	mov edx, DWORD PTR [esi+2024]
	mov eax, DWORD PTR [esi+1984]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2024]
	adc edx, DWORD PTR [esi+2028]
	add eax, DWORD PTR [esi+1984]
	adc edx, DWORD PTR [esi+1988]
	mov DWORD PTR [esi+1984], eax
	mov DWORD PTR [esi+1988], edx
	mov eax, DWORD PTR [esi+1976]
	mov edx, DWORD PTR [esi+1980]
	xor eax, DWORD PTR [esi+1984]
	xor edx, DWORD PTR [esi+1988]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1976], edx
	mov DWORD PTR [esi+1980], eax
	mov edx, DWORD PTR [esi+1976]
	mov eax, DWORD PTR [esi+1936]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1976]
	adc edx, DWORD PTR [esi+1980]
	add eax, DWORD PTR [esi+1936]
	adc edx, DWORD PTR [esi+1940]
	mov DWORD PTR [esi+1936], eax
	mov DWORD PTR [esi+1940], edx
	mov eax, DWORD PTR [esi+2024]
	mov edx, DWORD PTR [esi+2028]
	xor eax, DWORD PTR [esi+1936]
	xor edx, DWORD PTR [esi+1940]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2024], edx
	mov DWORD PTR [esi+2028], eax
	mov edx, DWORD PTR [esi+2024]
	mov eax, DWORD PTR [esi+1984]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2024]
	adc edx, DWORD PTR [esi+2028]
	add eax, DWORD PTR [esi+1984]
	adc edx, DWORD PTR [esi+1988]
	mov DWORD PTR [esi+1984], eax
	mov DWORD PTR [esi+1988], edx
	mov eax, DWORD PTR [esi+1976]
	mov edx, DWORD PTR [esi+1980]
	xor eax, DWORD PTR [esi+1984]
	xor edx, DWORD PTR [esi+1988]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1976], eax
	mov DWORD PTR [esi+1980], edx
	mov edx, DWORD PTR [esi+1952]
	mov eax, DWORD PTR [esi+1944]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1952]
	adc edx, DWORD PTR [esi+1956]
	add eax, DWORD PTR [esi+1944]
	adc edx, DWORD PTR [esi+1948]
	mov DWORD PTR [esi+1944], eax
	mov DWORD PTR [esi+1948], edx
	mov eax, DWORD PTR [esi+2032]
	mov edx, DWORD PTR [esi+2036]
	xor eax, DWORD PTR [esi+1944]
	xor edx, DWORD PTR [esi+1948]
	mov DWORD PTR [esi+2032], edx
	mov DWORD PTR [esi+2036], eax
	mov edx, DWORD PTR [esi+2032]
	mov eax, DWORD PTR [esi+1992]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2032]
	adc edx, DWORD PTR [esi+2036]
	add eax, DWORD PTR [esi+1992]
	adc edx, DWORD PTR [esi+1996]
	mov DWORD PTR [esi+1992], eax
	mov DWORD PTR [esi+1996], edx
	mov eax, DWORD PTR [esi+1952]
	mov edx, DWORD PTR [esi+1956]
	xor eax, DWORD PTR [esi+1992]
	xor edx, DWORD PTR [esi+1996]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1952], edx
	mov DWORD PTR [esi+1956], eax
	mov edx, DWORD PTR [esi+1952]
	mov eax, DWORD PTR [esi+1944]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1952]
	adc edx, DWORD PTR [esi+1956]
	add eax, DWORD PTR [esi+1944]
	adc edx, DWORD PTR [esi+1948]
	mov DWORD PTR [esi+1944], eax
	mov DWORD PTR [esi+1948], edx
	mov eax, DWORD PTR [esi+2032]
	mov edx, DWORD PTR [esi+2036]
	xor eax, DWORD PTR [esi+1944]
	xor edx, DWORD PTR [esi+1948]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2032], edx
	mov DWORD PTR [esi+2036], eax
	mov edx, DWORD PTR [esi+2032]
	mov eax, DWORD PTR [esi+1992]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2032]
	adc edx, DWORD PTR [esi+2036]
	add eax, DWORD PTR [esi+1992]
	adc edx, DWORD PTR [esi+1996]
	mov DWORD PTR [esi+1992], eax
	mov DWORD PTR [esi+1996], edx
	mov eax, DWORD PTR [esi+1952]
	mov edx, DWORD PTR [esi+1956]
	xor eax, DWORD PTR [esi+1992]
	xor edx, DWORD PTR [esi+1996]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1952], eax
	mov DWORD PTR [esi+1956], edx
	mov edx, DWORD PTR [esi+1280]
	mov eax, DWORD PTR [esi+1024]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1280]
	adc edx, DWORD PTR [esi+1284]
	add eax, DWORD PTR [esi+1024]
	adc edx, DWORD PTR [esi+1028]
	mov DWORD PTR [esi+1024], eax
	mov DWORD PTR [esi+1028], edx
	mov eax, DWORD PTR [esi+1792]
	mov edx, DWORD PTR [esi+1796]
	xor eax, DWORD PTR [esi+1024]
	xor edx, DWORD PTR [esi+1028]
	mov DWORD PTR [esi+1792], edx
	mov DWORD PTR [esi+1796], eax
	mov edx, DWORD PTR [esi+1792]
	mov eax, DWORD PTR [esi+1536]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1792]
	adc edx, DWORD PTR [esi+1796]
	add eax, DWORD PTR [esi+1536]
	adc edx, DWORD PTR [esi+1540]
	mov DWORD PTR [esi+1536], eax
	mov DWORD PTR [esi+1540], edx
	mov eax, DWORD PTR [esi+1280]
	mov edx, DWORD PTR [esi+1284]
	xor eax, DWORD PTR [esi+1536]
	xor edx, DWORD PTR [esi+1540]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1280], edx
	mov DWORD PTR [esi+1284], eax
	mov edx, DWORD PTR [esi+1280]
	mov eax, DWORD PTR [esi+1024]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1280]
	adc edx, DWORD PTR [esi+1284]
	add eax, DWORD PTR [esi+1024]
	adc edx, DWORD PTR [esi+1028]
	mov DWORD PTR [esi+1024], eax
	mov DWORD PTR [esi+1028], edx
	mov eax, DWORD PTR [esi+1792]
	mov edx, DWORD PTR [esi+1796]
	xor eax, DWORD PTR [esi+1024]
	xor edx, DWORD PTR [esi+1028]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1792], edx
	mov DWORD PTR [esi+1796], eax
	mov edx, DWORD PTR [esi+1792]
	mov eax, DWORD PTR [esi+1536]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1792]
	adc edx, DWORD PTR [esi+1796]
	add eax, DWORD PTR [esi+1536]
	adc edx, DWORD PTR [esi+1540]
	mov DWORD PTR [esi+1536], eax
	mov DWORD PTR [esi+1540], edx
	mov eax, DWORD PTR [esi+1280]
	mov edx, DWORD PTR [esi+1284]
	xor eax, DWORD PTR [esi+1536]
	xor edx, DWORD PTR [esi+1540]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1280], eax
	mov DWORD PTR [esi+1284], edx
	mov edx, DWORD PTR [esi+1288]
	mov eax, DWORD PTR [esi+1032]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1288]
	adc edx, DWORD PTR [esi+1292]
	add eax, DWORD PTR [esi+1032]
	adc edx, DWORD PTR [esi+1036]
	mov DWORD PTR [esi+1032], eax
	mov DWORD PTR [esi+1036], edx
	mov eax, DWORD PTR [esi+1800]
	mov edx, DWORD PTR [esi+1804]
	xor eax, DWORD PTR [esi+1032]
	xor edx, DWORD PTR [esi+1036]
	mov DWORD PTR [esi+1800], edx
	mov DWORD PTR [esi+1804], eax
	mov edx, DWORD PTR [esi+1800]
	mov eax, DWORD PTR [esi+1544]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1800]
	adc edx, DWORD PTR [esi+1804]
	add eax, DWORD PTR [esi+1544]
	adc edx, DWORD PTR [esi+1548]
	mov DWORD PTR [esi+1544], eax
	mov DWORD PTR [esi+1548], edx
	mov eax, DWORD PTR [esi+1288]
	mov edx, DWORD PTR [esi+1292]
	xor eax, DWORD PTR [esi+1544]
	xor edx, DWORD PTR [esi+1548]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1288], edx
	mov DWORD PTR [esi+1292], eax
	mov edx, DWORD PTR [esi+1288]
	mov eax, DWORD PTR [esi+1032]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1288]
	adc edx, DWORD PTR [esi+1292]
	add eax, DWORD PTR [esi+1032]
	adc edx, DWORD PTR [esi+1036]
	mov DWORD PTR [esi+1032], eax
	mov DWORD PTR [esi+1036], edx
	mov eax, DWORD PTR [esi+1800]
	mov edx, DWORD PTR [esi+1804]
	xor eax, DWORD PTR [esi+1032]
	xor edx, DWORD PTR [esi+1036]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1800], edx
	mov DWORD PTR [esi+1804], eax
	mov edx, DWORD PTR [esi+1800]
	mov eax, DWORD PTR [esi+1544]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1800]
	adc edx, DWORD PTR [esi+1804]
	add eax, DWORD PTR [esi+1544]
	adc edx, DWORD PTR [esi+1548]
	mov DWORD PTR [esi+1544], eax
	mov DWORD PTR [esi+1548], edx
	mov eax, DWORD PTR [esi+1288]
	mov edx, DWORD PTR [esi+1292]
	xor eax, DWORD PTR [esi+1544]
	xor edx, DWORD PTR [esi+1548]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1288], eax
	mov DWORD PTR [esi+1292], edx
	mov edx, DWORD PTR [esi+1408]
	mov eax, DWORD PTR [esi+1152]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1408]
	adc edx, DWORD PTR [esi+1412]
	add eax, DWORD PTR [esi+1152]
	adc edx, DWORD PTR [esi+1156]
	mov DWORD PTR [esi+1152], eax
	mov DWORD PTR [esi+1156], edx
	mov eax, DWORD PTR [esi+1920]
	mov edx, DWORD PTR [esi+1924]
	xor eax, DWORD PTR [esi+1152]
	xor edx, DWORD PTR [esi+1156]
	mov DWORD PTR [esi+1920], edx
	mov DWORD PTR [esi+1924], eax
	mov edx, DWORD PTR [esi+1920]
	mov eax, DWORD PTR [esi+1664]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1920]
	adc edx, DWORD PTR [esi+1924]
	add eax, DWORD PTR [esi+1664]
	adc edx, DWORD PTR [esi+1668]
	mov DWORD PTR [esi+1664], eax
	mov DWORD PTR [esi+1668], edx
	mov eax, DWORD PTR [esi+1408]
	mov edx, DWORD PTR [esi+1412]
	xor eax, DWORD PTR [esi+1664]
	xor edx, DWORD PTR [esi+1668]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1408], edx
	mov DWORD PTR [esi+1412], eax
	mov edx, DWORD PTR [esi+1408]
	mov eax, DWORD PTR [esi+1152]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1408]
	adc edx, DWORD PTR [esi+1412]
	add eax, DWORD PTR [esi+1152]
	adc edx, DWORD PTR [esi+1156]
	mov DWORD PTR [esi+1152], eax
	mov DWORD PTR [esi+1156], edx
	mov eax, DWORD PTR [esi+1920]
	mov edx, DWORD PTR [esi+1924]
	xor eax, DWORD PTR [esi+1152]
	xor edx, DWORD PTR [esi+1156]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1920], edx
	mov DWORD PTR [esi+1924], eax
	mov edx, DWORD PTR [esi+1920]
	mov eax, DWORD PTR [esi+1664]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1920]
	adc edx, DWORD PTR [esi+1924]
	add eax, DWORD PTR [esi+1664]
	adc edx, DWORD PTR [esi+1668]
	mov DWORD PTR [esi+1664], eax
	mov DWORD PTR [esi+1668], edx
	mov eax, DWORD PTR [esi+1408]
	mov edx, DWORD PTR [esi+1412]
	xor eax, DWORD PTR [esi+1664]
	xor edx, DWORD PTR [esi+1668]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1408], eax
	mov DWORD PTR [esi+1412], edx
	mov edx, DWORD PTR [esi+1416]
	mov eax, DWORD PTR [esi+1160]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1416]
	adc edx, DWORD PTR [esi+1420]
	add eax, DWORD PTR [esi+1160]
	adc edx, DWORD PTR [esi+1164]
	mov DWORD PTR [esi+1160], eax
	mov DWORD PTR [esi+1164], edx
	mov eax, DWORD PTR [esi+1928]
	mov edx, DWORD PTR [esi+1932]
	xor eax, DWORD PTR [esi+1160]
	xor edx, DWORD PTR [esi+1164]
	mov DWORD PTR [esi+1928], edx
	mov DWORD PTR [esi+1932], eax
	mov edx, DWORD PTR [esi+1928]
	mov eax, DWORD PTR [esi+1672]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1928]
	adc edx, DWORD PTR [esi+1932]
	add eax, DWORD PTR [esi+1672]
	adc edx, DWORD PTR [esi+1676]
	mov DWORD PTR [esi+1672], eax
	mov DWORD PTR [esi+1676], edx
	mov eax, DWORD PTR [esi+1416]
	mov edx, DWORD PTR [esi+1420]
	xor eax, DWORD PTR [esi+1672]
	xor edx, DWORD PTR [esi+1676]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1416], edx
	mov DWORD PTR [esi+1420], eax
	mov edx, DWORD PTR [esi+1416]
	mov eax, DWORD PTR [esi+1160]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1416]
	adc edx, DWORD PTR [esi+1420]
	add eax, DWORD PTR [esi+1160]
	adc edx, DWORD PTR [esi+1164]
	mov DWORD PTR [esi+1160], eax
	mov DWORD PTR [esi+1164], edx
	mov eax, DWORD PTR [esi+1928]
	mov edx, DWORD PTR [esi+1932]
	xor eax, DWORD PTR [esi+1160]
	xor edx, DWORD PTR [esi+1164]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1928], edx
	mov DWORD PTR [esi+1932], eax
	mov edx, DWORD PTR [esi+1928]
	mov eax, DWORD PTR [esi+1672]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1928]
	adc edx, DWORD PTR [esi+1932]
	add eax, DWORD PTR [esi+1672]
	adc edx, DWORD PTR [esi+1676]
	mov DWORD PTR [esi+1672], eax
	mov DWORD PTR [esi+1676], edx
	mov eax, DWORD PTR [esi+1416]
	mov edx, DWORD PTR [esi+1420]
	xor eax, DWORD PTR [esi+1672]
	xor edx, DWORD PTR [esi+1676]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1416], eax
	mov DWORD PTR [esi+1420], edx
	mov edx, DWORD PTR [esi+1288]
	mov eax, DWORD PTR [esi+1024]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1288]
	adc edx, DWORD PTR [esi+1292]
	add eax, DWORD PTR [esi+1024]
	adc edx, DWORD PTR [esi+1028]
	mov DWORD PTR [esi+1024], eax
	mov DWORD PTR [esi+1028], edx
	mov eax, DWORD PTR [esi+1928]
	mov edx, DWORD PTR [esi+1932]
	xor eax, DWORD PTR [esi+1024]
	xor edx, DWORD PTR [esi+1028]
	mov DWORD PTR [esi+1928], edx
	mov DWORD PTR [esi+1932], eax
	mov edx, DWORD PTR [esi+1928]
	mov eax, DWORD PTR [esi+1664]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1928]
	adc edx, DWORD PTR [esi+1932]
	add eax, DWORD PTR [esi+1664]
	adc edx, DWORD PTR [esi+1668]
	mov DWORD PTR [esi+1664], eax
	mov DWORD PTR [esi+1668], edx
	mov eax, DWORD PTR [esi+1288]
	mov edx, DWORD PTR [esi+1292]
	xor eax, DWORD PTR [esi+1664]
	xor edx, DWORD PTR [esi+1668]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1288], edx
	mov DWORD PTR [esi+1292], eax
	mov edx, DWORD PTR [esi+1288]
	mov eax, DWORD PTR [esi+1024]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1288]
	adc edx, DWORD PTR [esi+1292]
	add eax, DWORD PTR [esi+1024]
	adc edx, DWORD PTR [esi+1028]
	mov DWORD PTR [esi+1024], eax
	mov DWORD PTR [esi+1028], edx
	mov eax, DWORD PTR [esi+1928]
	mov edx, DWORD PTR [esi+1932]
	xor eax, DWORD PTR [esi+1024]
	xor edx, DWORD PTR [esi+1028]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1928], edx
	mov DWORD PTR [esi+1932], eax
	mov edx, DWORD PTR [esi+1928]
	mov eax, DWORD PTR [esi+1664]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1928]
	adc edx, DWORD PTR [esi+1932]
	add eax, DWORD PTR [esi+1664]
	adc edx, DWORD PTR [esi+1668]
	mov DWORD PTR [esi+1664], eax
	mov DWORD PTR [esi+1668], edx
	mov eax, DWORD PTR [esi+1288]
	mov edx, DWORD PTR [esi+1292]
	xor eax, DWORD PTR [esi+1664]
	xor edx, DWORD PTR [esi+1668]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1288], eax
	mov DWORD PTR [esi+1292], edx
	mov edx, DWORD PTR [esi+1408]
	mov eax, DWORD PTR [esi+1032]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1408]
	adc edx, DWORD PTR [esi+1412]
	add eax, DWORD PTR [esi+1032]
	adc edx, DWORD PTR [esi+1036]
	mov DWORD PTR [esi+1032], eax
	mov DWORD PTR [esi+1036], edx
	mov eax, DWORD PTR [esi+1792]
	mov edx, DWORD PTR [esi+1796]
	xor eax, DWORD PTR [esi+1032]
	xor edx, DWORD PTR [esi+1036]
	mov DWORD PTR [esi+1792], edx
	mov DWORD PTR [esi+1796], eax
	mov edx, DWORD PTR [esi+1792]
	mov eax, DWORD PTR [esi+1672]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1792]
	adc edx, DWORD PTR [esi+1796]
	add eax, DWORD PTR [esi+1672]
	adc edx, DWORD PTR [esi+1676]
	mov DWORD PTR [esi+1672], eax
	mov DWORD PTR [esi+1676], edx
	mov eax, DWORD PTR [esi+1408]
	mov edx, DWORD PTR [esi+1412]
	xor eax, DWORD PTR [esi+1672]
	xor edx, DWORD PTR [esi+1676]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1408], edx
	mov DWORD PTR [esi+1412], eax
	mov edx, DWORD PTR [esi+1408]
	mov eax, DWORD PTR [esi+1032]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1408]
	adc edx, DWORD PTR [esi+1412]
	add eax, DWORD PTR [esi+1032]
	adc edx, DWORD PTR [esi+1036]
	mov DWORD PTR [esi+1032], eax
	mov DWORD PTR [esi+1036], edx
	mov eax, DWORD PTR [esi+1792]
	mov edx, DWORD PTR [esi+1796]
	xor eax, DWORD PTR [esi+1032]
	xor edx, DWORD PTR [esi+1036]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1792], edx
	mov DWORD PTR [esi+1796], eax
	mov edx, DWORD PTR [esi+1792]
	mov eax, DWORD PTR [esi+1672]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1792]
	adc edx, DWORD PTR [esi+1796]
	add eax, DWORD PTR [esi+1672]
	adc edx, DWORD PTR [esi+1676]
	mov DWORD PTR [esi+1672], eax
	mov DWORD PTR [esi+1676], edx
	mov eax, DWORD PTR [esi+1408]
	mov edx, DWORD PTR [esi+1412]
	xor eax, DWORD PTR [esi+1672]
	xor edx, DWORD PTR [esi+1676]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1408], eax
	mov DWORD PTR [esi+1412], edx
	mov edx, DWORD PTR [esi+1416]
	mov eax, DWORD PTR [esi+1152]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1416]
	adc edx, DWORD PTR [esi+1420]
	add eax, DWORD PTR [esi+1152]
	adc edx, DWORD PTR [esi+1156]
	mov DWORD PTR [esi+1152], eax
	mov DWORD PTR [esi+1156], edx
	mov eax, DWORD PTR [esi+1800]
	mov edx, DWORD PTR [esi+1804]
	xor eax, DWORD PTR [esi+1152]
	xor edx, DWORD PTR [esi+1156]
	mov DWORD PTR [esi+1800], edx
	mov DWORD PTR [esi+1804], eax
	mov edx, DWORD PTR [esi+1800]
	mov eax, DWORD PTR [esi+1536]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1800]
	adc edx, DWORD PTR [esi+1804]
	add eax, DWORD PTR [esi+1536]
	adc edx, DWORD PTR [esi+1540]
	mov DWORD PTR [esi+1536], eax
	mov DWORD PTR [esi+1540], edx
	mov eax, DWORD PTR [esi+1416]
	mov edx, DWORD PTR [esi+1420]
	xor eax, DWORD PTR [esi+1536]
	xor edx, DWORD PTR [esi+1540]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1416], edx
	mov DWORD PTR [esi+1420], eax
	mov edx, DWORD PTR [esi+1416]
	mov eax, DWORD PTR [esi+1152]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1416]
	adc edx, DWORD PTR [esi+1420]
	add eax, DWORD PTR [esi+1152]
	adc edx, DWORD PTR [esi+1156]
	mov DWORD PTR [esi+1152], eax
	mov DWORD PTR [esi+1156], edx
	mov eax, DWORD PTR [esi+1800]
	mov edx, DWORD PTR [esi+1804]
	xor eax, DWORD PTR [esi+1152]
	xor edx, DWORD PTR [esi+1156]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1800], edx
	mov DWORD PTR [esi+1804], eax
	mov edx, DWORD PTR [esi+1800]
	mov eax, DWORD PTR [esi+1536]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1800]
	adc edx, DWORD PTR [esi+1804]
	add eax, DWORD PTR [esi+1536]
	adc edx, DWORD PTR [esi+1540]
	mov DWORD PTR [esi+1536], eax
	mov DWORD PTR [esi+1540], edx
	mov eax, DWORD PTR [esi+1416]
	mov edx, DWORD PTR [esi+1420]
	xor eax, DWORD PTR [esi+1536]
	xor edx, DWORD PTR [esi+1540]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1416], eax
	mov DWORD PTR [esi+1420], edx
	mov edx, DWORD PTR [esi+1280]
	mov eax, DWORD PTR [esi+1160]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1280]
	adc edx, DWORD PTR [esi+1284]
	add eax, DWORD PTR [esi+1160]
	adc edx, DWORD PTR [esi+1164]
	mov DWORD PTR [esi+1160], eax
	mov DWORD PTR [esi+1164], edx
	mov eax, DWORD PTR [esi+1920]
	mov edx, DWORD PTR [esi+1924]
	xor eax, DWORD PTR [esi+1160]
	xor edx, DWORD PTR [esi+1164]
	mov DWORD PTR [esi+1920], edx
	mov DWORD PTR [esi+1924], eax
	mov edx, DWORD PTR [esi+1920]
	mov eax, DWORD PTR [esi+1544]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1920]
	adc edx, DWORD PTR [esi+1924]
	add eax, DWORD PTR [esi+1544]
	adc edx, DWORD PTR [esi+1548]
	mov DWORD PTR [esi+1544], eax
	mov DWORD PTR [esi+1548], edx
	mov eax, DWORD PTR [esi+1280]
	mov edx, DWORD PTR [esi+1284]
	xor eax, DWORD PTR [esi+1544]
	xor edx, DWORD PTR [esi+1548]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1280], edx
	mov DWORD PTR [esi+1284], eax
	mov edx, DWORD PTR [esi+1280]
	mov eax, DWORD PTR [esi+1160]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1280]
	adc edx, DWORD PTR [esi+1284]
	add eax, DWORD PTR [esi+1160]
	adc edx, DWORD PTR [esi+1164]
	mov DWORD PTR [esi+1160], eax
	mov DWORD PTR [esi+1164], edx
	mov eax, DWORD PTR [esi+1920]
	mov edx, DWORD PTR [esi+1924]
	xor eax, DWORD PTR [esi+1160]
	xor edx, DWORD PTR [esi+1164]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1920], edx
	mov DWORD PTR [esi+1924], eax
	mov edx, DWORD PTR [esi+1920]
	mov eax, DWORD PTR [esi+1544]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1920]
	adc edx, DWORD PTR [esi+1924]
	add eax, DWORD PTR [esi+1544]
	adc edx, DWORD PTR [esi+1548]
	mov DWORD PTR [esi+1544], eax
	mov DWORD PTR [esi+1548], edx
	mov eax, DWORD PTR [esi+1280]
	mov edx, DWORD PTR [esi+1284]
	xor eax, DWORD PTR [esi+1544]
	xor edx, DWORD PTR [esi+1548]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1280], eax
	mov DWORD PTR [esi+1284], edx
	mov edx, DWORD PTR [esi+1296]
	mov eax, DWORD PTR [esi+1040]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1296]
	adc edx, DWORD PTR [esi+1300]
	add eax, DWORD PTR [esi+1040]
	adc edx, DWORD PTR [esi+1044]
	mov DWORD PTR [esi+1040], eax
	mov DWORD PTR [esi+1044], edx
	mov eax, DWORD PTR [esi+1808]
	mov edx, DWORD PTR [esi+1812]
	xor eax, DWORD PTR [esi+1040]
	xor edx, DWORD PTR [esi+1044]
	mov DWORD PTR [esi+1808], edx
	mov DWORD PTR [esi+1812], eax
	mov edx, DWORD PTR [esi+1808]
	mov eax, DWORD PTR [esi+1552]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1808]
	adc edx, DWORD PTR [esi+1812]
	add eax, DWORD PTR [esi+1552]
	adc edx, DWORD PTR [esi+1556]
	mov DWORD PTR [esi+1552], eax
	mov DWORD PTR [esi+1556], edx
	mov eax, DWORD PTR [esi+1296]
	mov edx, DWORD PTR [esi+1300]
	xor eax, DWORD PTR [esi+1552]
	xor edx, DWORD PTR [esi+1556]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1296], edx
	mov DWORD PTR [esi+1300], eax
	mov edx, DWORD PTR [esi+1296]
	mov eax, DWORD PTR [esi+1040]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1296]
	adc edx, DWORD PTR [esi+1300]
	add eax, DWORD PTR [esi+1040]
	adc edx, DWORD PTR [esi+1044]
	mov DWORD PTR [esi+1040], eax
	mov DWORD PTR [esi+1044], edx
	mov eax, DWORD PTR [esi+1808]
	mov edx, DWORD PTR [esi+1812]
	xor eax, DWORD PTR [esi+1040]
	xor edx, DWORD PTR [esi+1044]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1808], edx
	mov DWORD PTR [esi+1812], eax
	mov edx, DWORD PTR [esi+1808]
	mov eax, DWORD PTR [esi+1552]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1808]
	adc edx, DWORD PTR [esi+1812]
	add eax, DWORD PTR [esi+1552]
	adc edx, DWORD PTR [esi+1556]
	mov DWORD PTR [esi+1552], eax
	mov DWORD PTR [esi+1556], edx
	mov eax, DWORD PTR [esi+1296]
	mov edx, DWORD PTR [esi+1300]
	xor eax, DWORD PTR [esi+1552]
	xor edx, DWORD PTR [esi+1556]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1296], eax
	mov DWORD PTR [esi+1300], edx
	mov edx, DWORD PTR [esi+1304]
	mov eax, DWORD PTR [esi+1048]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1304]
	adc edx, DWORD PTR [esi+1308]
	add eax, DWORD PTR [esi+1048]
	adc edx, DWORD PTR [esi+1052]
	mov DWORD PTR [esi+1048], eax
	mov DWORD PTR [esi+1052], edx
	mov eax, DWORD PTR [esi+1816]
	mov edx, DWORD PTR [esi+1820]
	xor eax, DWORD PTR [esi+1048]
	xor edx, DWORD PTR [esi+1052]
	mov DWORD PTR [esi+1816], edx
	mov DWORD PTR [esi+1820], eax
	mov edx, DWORD PTR [esi+1816]
	mov eax, DWORD PTR [esi+1560]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1816]
	adc edx, DWORD PTR [esi+1820]
	add eax, DWORD PTR [esi+1560]
	adc edx, DWORD PTR [esi+1564]
	mov DWORD PTR [esi+1560], eax
	mov DWORD PTR [esi+1564], edx
	mov eax, DWORD PTR [esi+1304]
	mov edx, DWORD PTR [esi+1308]
	xor eax, DWORD PTR [esi+1560]
	xor edx, DWORD PTR [esi+1564]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1304], edx
	mov DWORD PTR [esi+1308], eax
	mov edx, DWORD PTR [esi+1304]
	mov eax, DWORD PTR [esi+1048]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1304]
	adc edx, DWORD PTR [esi+1308]
	add eax, DWORD PTR [esi+1048]
	adc edx, DWORD PTR [esi+1052]
	mov DWORD PTR [esi+1048], eax
	mov DWORD PTR [esi+1052], edx
	mov eax, DWORD PTR [esi+1816]
	mov edx, DWORD PTR [esi+1820]
	xor eax, DWORD PTR [esi+1048]
	xor edx, DWORD PTR [esi+1052]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1816], edx
	mov DWORD PTR [esi+1820], eax
	mov edx, DWORD PTR [esi+1816]
	mov eax, DWORD PTR [esi+1560]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1816]
	adc edx, DWORD PTR [esi+1820]
	add eax, DWORD PTR [esi+1560]
	adc edx, DWORD PTR [esi+1564]
	mov DWORD PTR [esi+1560], eax
	mov DWORD PTR [esi+1564], edx
	mov eax, DWORD PTR [esi+1304]
	mov edx, DWORD PTR [esi+1308]
	xor eax, DWORD PTR [esi+1560]
	xor edx, DWORD PTR [esi+1564]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1304], eax
	mov DWORD PTR [esi+1308], edx
	mov edx, DWORD PTR [esi+1424]
	mov eax, DWORD PTR [esi+1168]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1424]
	adc edx, DWORD PTR [esi+1428]
	add eax, DWORD PTR [esi+1168]
	adc edx, DWORD PTR [esi+1172]
	mov DWORD PTR [esi+1168], eax
	mov DWORD PTR [esi+1172], edx
	mov eax, DWORD PTR [esi+1936]
	mov edx, DWORD PTR [esi+1940]
	xor eax, DWORD PTR [esi+1168]
	xor edx, DWORD PTR [esi+1172]
	mov DWORD PTR [esi+1936], edx
	mov DWORD PTR [esi+1940], eax
	mov edx, DWORD PTR [esi+1936]
	mov eax, DWORD PTR [esi+1680]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1936]
	adc edx, DWORD PTR [esi+1940]
	add eax, DWORD PTR [esi+1680]
	adc edx, DWORD PTR [esi+1684]
	mov DWORD PTR [esi+1680], eax
	mov DWORD PTR [esi+1684], edx
	mov eax, DWORD PTR [esi+1424]
	mov edx, DWORD PTR [esi+1428]
	xor eax, DWORD PTR [esi+1680]
	xor edx, DWORD PTR [esi+1684]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1424], edx
	mov DWORD PTR [esi+1428], eax
	mov edx, DWORD PTR [esi+1424]
	mov eax, DWORD PTR [esi+1168]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1424]
	adc edx, DWORD PTR [esi+1428]
	add eax, DWORD PTR [esi+1168]
	adc edx, DWORD PTR [esi+1172]
	mov DWORD PTR [esi+1168], eax
	mov DWORD PTR [esi+1172], edx
	mov eax, DWORD PTR [esi+1936]
	mov edx, DWORD PTR [esi+1940]
	xor eax, DWORD PTR [esi+1168]
	xor edx, DWORD PTR [esi+1172]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1936], edx
	mov DWORD PTR [esi+1940], eax
	mov edx, DWORD PTR [esi+1936]
	mov eax, DWORD PTR [esi+1680]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1936]
	adc edx, DWORD PTR [esi+1940]
	add eax, DWORD PTR [esi+1680]
	adc edx, DWORD PTR [esi+1684]
	mov DWORD PTR [esi+1680], eax
	mov DWORD PTR [esi+1684], edx
	mov eax, DWORD PTR [esi+1424]
	mov edx, DWORD PTR [esi+1428]
	xor eax, DWORD PTR [esi+1680]
	xor edx, DWORD PTR [esi+1684]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1424], eax
	mov DWORD PTR [esi+1428], edx
	mov edx, DWORD PTR [esi+1432]
	mov eax, DWORD PTR [esi+1176]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1432]
	adc edx, DWORD PTR [esi+1436]
	add eax, DWORD PTR [esi+1176]
	adc edx, DWORD PTR [esi+1180]
	mov DWORD PTR [esi+1176], eax
	mov DWORD PTR [esi+1180], edx
	mov eax, DWORD PTR [esi+1944]
	mov edx, DWORD PTR [esi+1948]
	xor eax, DWORD PTR [esi+1176]
	xor edx, DWORD PTR [esi+1180]
	mov DWORD PTR [esi+1944], edx
	mov DWORD PTR [esi+1948], eax
	mov edx, DWORD PTR [esi+1944]
	mov eax, DWORD PTR [esi+1688]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1944]
	adc edx, DWORD PTR [esi+1948]
	add eax, DWORD PTR [esi+1688]
	adc edx, DWORD PTR [esi+1692]
	mov DWORD PTR [esi+1688], eax
	mov DWORD PTR [esi+1692], edx
	mov eax, DWORD PTR [esi+1432]
	mov edx, DWORD PTR [esi+1436]
	xor eax, DWORD PTR [esi+1688]
	xor edx, DWORD PTR [esi+1692]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1432], edx
	mov DWORD PTR [esi+1436], eax
	mov edx, DWORD PTR [esi+1432]
	mov eax, DWORD PTR [esi+1176]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1432]
	adc edx, DWORD PTR [esi+1436]
	add eax, DWORD PTR [esi+1176]
	adc edx, DWORD PTR [esi+1180]
	mov DWORD PTR [esi+1176], eax
	mov DWORD PTR [esi+1180], edx
	mov eax, DWORD PTR [esi+1944]
	mov edx, DWORD PTR [esi+1948]
	xor eax, DWORD PTR [esi+1176]
	xor edx, DWORD PTR [esi+1180]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1944], edx
	mov DWORD PTR [esi+1948], eax
	mov edx, DWORD PTR [esi+1944]
	mov eax, DWORD PTR [esi+1688]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1944]
	adc edx, DWORD PTR [esi+1948]
	add eax, DWORD PTR [esi+1688]
	adc edx, DWORD PTR [esi+1692]
	mov DWORD PTR [esi+1688], eax
	mov DWORD PTR [esi+1692], edx
	mov eax, DWORD PTR [esi+1432]
	mov edx, DWORD PTR [esi+1436]
	xor eax, DWORD PTR [esi+1688]
	xor edx, DWORD PTR [esi+1692]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1432], eax
	mov DWORD PTR [esi+1436], edx
	mov edx, DWORD PTR [esi+1304]
	mov eax, DWORD PTR [esi+1040]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1304]
	adc edx, DWORD PTR [esi+1308]
	add eax, DWORD PTR [esi+1040]
	adc edx, DWORD PTR [esi+1044]
	mov DWORD PTR [esi+1040], eax
	mov DWORD PTR [esi+1044], edx
	mov eax, DWORD PTR [esi+1944]
	mov edx, DWORD PTR [esi+1948]
	xor eax, DWORD PTR [esi+1040]
	xor edx, DWORD PTR [esi+1044]
	mov DWORD PTR [esi+1944], edx
	mov DWORD PTR [esi+1948], eax
	mov edx, DWORD PTR [esi+1944]
	mov eax, DWORD PTR [esi+1680]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1944]
	adc edx, DWORD PTR [esi+1948]
	add eax, DWORD PTR [esi+1680]
	adc edx, DWORD PTR [esi+1684]
	mov DWORD PTR [esi+1680], eax
	mov DWORD PTR [esi+1684], edx
	mov eax, DWORD PTR [esi+1304]
	mov edx, DWORD PTR [esi+1308]
	xor eax, DWORD PTR [esi+1680]
	xor edx, DWORD PTR [esi+1684]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1304], edx
	mov DWORD PTR [esi+1308], eax
	mov edx, DWORD PTR [esi+1304]
	mov eax, DWORD PTR [esi+1040]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1304]
	adc edx, DWORD PTR [esi+1308]
	add eax, DWORD PTR [esi+1040]
	adc edx, DWORD PTR [esi+1044]
	mov DWORD PTR [esi+1040], eax
	mov DWORD PTR [esi+1044], edx
	mov eax, DWORD PTR [esi+1944]
	mov edx, DWORD PTR [esi+1948]
	xor eax, DWORD PTR [esi+1040]
	xor edx, DWORD PTR [esi+1044]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1944], edx
	mov DWORD PTR [esi+1948], eax
	mov edx, DWORD PTR [esi+1944]
	mov eax, DWORD PTR [esi+1680]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1944]
	adc edx, DWORD PTR [esi+1948]
	add eax, DWORD PTR [esi+1680]
	adc edx, DWORD PTR [esi+1684]
	mov DWORD PTR [esi+1680], eax
	mov DWORD PTR [esi+1684], edx
	mov eax, DWORD PTR [esi+1304]
	mov edx, DWORD PTR [esi+1308]
	xor eax, DWORD PTR [esi+1680]
	xor edx, DWORD PTR [esi+1684]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1304], eax
	mov DWORD PTR [esi+1308], edx
	mov edx, DWORD PTR [esi+1424]
	mov eax, DWORD PTR [esi+1048]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1424]
	adc edx, DWORD PTR [esi+1428]
	add eax, DWORD PTR [esi+1048]
	adc edx, DWORD PTR [esi+1052]
	mov DWORD PTR [esi+1048], eax
	mov DWORD PTR [esi+1052], edx
	mov eax, DWORD PTR [esi+1808]
	mov edx, DWORD PTR [esi+1812]
	xor eax, DWORD PTR [esi+1048]
	xor edx, DWORD PTR [esi+1052]
	mov DWORD PTR [esi+1808], edx
	mov DWORD PTR [esi+1812], eax
	mov edx, DWORD PTR [esi+1808]
	mov eax, DWORD PTR [esi+1688]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1808]
	adc edx, DWORD PTR [esi+1812]
	add eax, DWORD PTR [esi+1688]
	adc edx, DWORD PTR [esi+1692]
	mov DWORD PTR [esi+1688], eax
	mov DWORD PTR [esi+1692], edx
	mov eax, DWORD PTR [esi+1424]
	mov edx, DWORD PTR [esi+1428]
	xor eax, DWORD PTR [esi+1688]
	xor edx, DWORD PTR [esi+1692]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1424], edx
	mov DWORD PTR [esi+1428], eax
	mov edx, DWORD PTR [esi+1424]
	mov eax, DWORD PTR [esi+1048]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1424]
	adc edx, DWORD PTR [esi+1428]
	add eax, DWORD PTR [esi+1048]
	adc edx, DWORD PTR [esi+1052]
	mov DWORD PTR [esi+1048], eax
	mov DWORD PTR [esi+1052], edx
	mov eax, DWORD PTR [esi+1808]
	mov edx, DWORD PTR [esi+1812]
	xor eax, DWORD PTR [esi+1048]
	xor edx, DWORD PTR [esi+1052]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1808], edx
	mov DWORD PTR [esi+1812], eax
	mov edx, DWORD PTR [esi+1808]
	mov eax, DWORD PTR [esi+1688]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1808]
	adc edx, DWORD PTR [esi+1812]
	add eax, DWORD PTR [esi+1688]
	adc edx, DWORD PTR [esi+1692]
	mov DWORD PTR [esi+1688], eax
	mov DWORD PTR [esi+1692], edx
	mov eax, DWORD PTR [esi+1424]
	mov edx, DWORD PTR [esi+1428]
	xor eax, DWORD PTR [esi+1688]
	xor edx, DWORD PTR [esi+1692]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1424], eax
	mov DWORD PTR [esi+1428], edx
	mov edx, DWORD PTR [esi+1432]
	mov eax, DWORD PTR [esi+1168]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1432]
	adc edx, DWORD PTR [esi+1436]
	add eax, DWORD PTR [esi+1168]
	adc edx, DWORD PTR [esi+1172]
	mov DWORD PTR [esi+1168], eax
	mov DWORD PTR [esi+1172], edx
	mov eax, DWORD PTR [esi+1816]
	mov edx, DWORD PTR [esi+1820]
	xor eax, DWORD PTR [esi+1168]
	xor edx, DWORD PTR [esi+1172]
	mov DWORD PTR [esi+1816], edx
	mov DWORD PTR [esi+1820], eax
	mov edx, DWORD PTR [esi+1816]
	mov eax, DWORD PTR [esi+1552]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1816]
	adc edx, DWORD PTR [esi+1820]
	add eax, DWORD PTR [esi+1552]
	adc edx, DWORD PTR [esi+1556]
	mov DWORD PTR [esi+1552], eax
	mov DWORD PTR [esi+1556], edx
	mov eax, DWORD PTR [esi+1432]
	mov edx, DWORD PTR [esi+1436]
	xor eax, DWORD PTR [esi+1552]
	xor edx, DWORD PTR [esi+1556]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1432], edx
	mov DWORD PTR [esi+1436], eax
	mov edx, DWORD PTR [esi+1432]
	mov eax, DWORD PTR [esi+1168]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1432]
	adc edx, DWORD PTR [esi+1436]
	add eax, DWORD PTR [esi+1168]
	adc edx, DWORD PTR [esi+1172]
	mov DWORD PTR [esi+1168], eax
	mov DWORD PTR [esi+1172], edx
	mov eax, DWORD PTR [esi+1816]
	mov edx, DWORD PTR [esi+1820]
	xor eax, DWORD PTR [esi+1168]
	xor edx, DWORD PTR [esi+1172]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1816], edx
	mov DWORD PTR [esi+1820], eax
	mov edx, DWORD PTR [esi+1816]
	mov eax, DWORD PTR [esi+1552]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1816]
	adc edx, DWORD PTR [esi+1820]
	add eax, DWORD PTR [esi+1552]
	adc edx, DWORD PTR [esi+1556]
	mov DWORD PTR [esi+1552], eax
	mov DWORD PTR [esi+1556], edx
	mov eax, DWORD PTR [esi+1432]
	mov edx, DWORD PTR [esi+1436]
	xor eax, DWORD PTR [esi+1552]
	xor edx, DWORD PTR [esi+1556]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1432], eax
	mov DWORD PTR [esi+1436], edx
	mov edx, DWORD PTR [esi+1296]
	mov eax, DWORD PTR [esi+1176]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1296]
	adc edx, DWORD PTR [esi+1300]
	add eax, DWORD PTR [esi+1176]
	adc edx, DWORD PTR [esi+1180]
	mov DWORD PTR [esi+1176], eax
	mov DWORD PTR [esi+1180], edx
	mov eax, DWORD PTR [esi+1936]
	mov edx, DWORD PTR [esi+1940]
	xor eax, DWORD PTR [esi+1176]
	xor edx, DWORD PTR [esi+1180]
	mov DWORD PTR [esi+1936], edx
	mov DWORD PTR [esi+1940], eax
	mov edx, DWORD PTR [esi+1936]
	mov eax, DWORD PTR [esi+1560]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1936]
	adc edx, DWORD PTR [esi+1940]
	add eax, DWORD PTR [esi+1560]
	adc edx, DWORD PTR [esi+1564]
	mov DWORD PTR [esi+1560], eax
	mov DWORD PTR [esi+1564], edx
	mov eax, DWORD PTR [esi+1296]
	mov edx, DWORD PTR [esi+1300]
	xor eax, DWORD PTR [esi+1560]
	xor edx, DWORD PTR [esi+1564]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1296], edx
	mov DWORD PTR [esi+1300], eax
	mov edx, DWORD PTR [esi+1296]
	mov eax, DWORD PTR [esi+1176]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1296]
	adc edx, DWORD PTR [esi+1300]
	add eax, DWORD PTR [esi+1176]
	adc edx, DWORD PTR [esi+1180]
	mov DWORD PTR [esi+1176], eax
	mov DWORD PTR [esi+1180], edx
	mov eax, DWORD PTR [esi+1936]
	mov edx, DWORD PTR [esi+1940]
	xor eax, DWORD PTR [esi+1176]
	xor edx, DWORD PTR [esi+1180]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1936], edx
	mov DWORD PTR [esi+1940], eax
	mov edx, DWORD PTR [esi+1936]
	mov eax, DWORD PTR [esi+1560]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1936]
	adc edx, DWORD PTR [esi+1940]
	add eax, DWORD PTR [esi+1560]
	adc edx, DWORD PTR [esi+1564]
	mov DWORD PTR [esi+1560], eax
	mov DWORD PTR [esi+1564], edx
	mov eax, DWORD PTR [esi+1296]
	mov edx, DWORD PTR [esi+1300]
	xor eax, DWORD PTR [esi+1560]
	xor edx, DWORD PTR [esi+1564]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1296], eax
	mov DWORD PTR [esi+1300], edx
	mov edx, DWORD PTR [esi+1312]
	mov eax, DWORD PTR [esi+1056]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1312]
	adc edx, DWORD PTR [esi+1316]
	add eax, DWORD PTR [esi+1056]
	adc edx, DWORD PTR [esi+1060]
	mov DWORD PTR [esi+1056], eax
	mov DWORD PTR [esi+1060], edx
	mov eax, DWORD PTR [esi+1824]
	mov edx, DWORD PTR [esi+1828]
	xor eax, DWORD PTR [esi+1056]
	xor edx, DWORD PTR [esi+1060]
	mov DWORD PTR [esi+1824], edx
	mov DWORD PTR [esi+1828], eax
	mov edx, DWORD PTR [esi+1824]
	mov eax, DWORD PTR [esi+1568]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1824]
	adc edx, DWORD PTR [esi+1828]
	add eax, DWORD PTR [esi+1568]
	adc edx, DWORD PTR [esi+1572]
	mov DWORD PTR [esi+1568], eax
	mov DWORD PTR [esi+1572], edx
	mov eax, DWORD PTR [esi+1312]
	mov edx, DWORD PTR [esi+1316]
	xor eax, DWORD PTR [esi+1568]
	xor edx, DWORD PTR [esi+1572]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1312], edx
	mov DWORD PTR [esi+1316], eax
	mov edx, DWORD PTR [esi+1312]
	mov eax, DWORD PTR [esi+1056]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1312]
	adc edx, DWORD PTR [esi+1316]
	add eax, DWORD PTR [esi+1056]
	adc edx, DWORD PTR [esi+1060]
	mov DWORD PTR [esi+1056], eax
	mov DWORD PTR [esi+1060], edx
	mov eax, DWORD PTR [esi+1824]
	mov edx, DWORD PTR [esi+1828]
	xor eax, DWORD PTR [esi+1056]
	xor edx, DWORD PTR [esi+1060]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1824], edx
	mov DWORD PTR [esi+1828], eax
	mov edx, DWORD PTR [esi+1824]
	mov eax, DWORD PTR [esi+1568]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1824]
	adc edx, DWORD PTR [esi+1828]
	add eax, DWORD PTR [esi+1568]
	adc edx, DWORD PTR [esi+1572]
	mov DWORD PTR [esi+1568], eax
	mov DWORD PTR [esi+1572], edx
	mov eax, DWORD PTR [esi+1312]
	mov edx, DWORD PTR [esi+1316]
	xor eax, DWORD PTR [esi+1568]
	xor edx, DWORD PTR [esi+1572]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1312], eax
	mov DWORD PTR [esi+1316], edx
	mov edx, DWORD PTR [esi+1320]
	mov eax, DWORD PTR [esi+1064]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1320]
	adc edx, DWORD PTR [esi+1324]
	add eax, DWORD PTR [esi+1064]
	adc edx, DWORD PTR [esi+1068]
	mov DWORD PTR [esi+1064], eax
	mov DWORD PTR [esi+1068], edx
	mov eax, DWORD PTR [esi+1832]
	mov edx, DWORD PTR [esi+1836]
	xor eax, DWORD PTR [esi+1064]
	xor edx, DWORD PTR [esi+1068]
	mov DWORD PTR [esi+1832], edx
	mov DWORD PTR [esi+1836], eax
	mov edx, DWORD PTR [esi+1832]
	mov eax, DWORD PTR [esi+1576]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1832]
	adc edx, DWORD PTR [esi+1836]
	add eax, DWORD PTR [esi+1576]
	adc edx, DWORD PTR [esi+1580]
	mov DWORD PTR [esi+1576], eax
	mov DWORD PTR [esi+1580], edx
	mov eax, DWORD PTR [esi+1320]
	mov edx, DWORD PTR [esi+1324]
	xor eax, DWORD PTR [esi+1576]
	xor edx, DWORD PTR [esi+1580]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1320], edx
	mov DWORD PTR [esi+1324], eax
	mov edx, DWORD PTR [esi+1320]
	mov eax, DWORD PTR [esi+1064]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1320]
	adc edx, DWORD PTR [esi+1324]
	add eax, DWORD PTR [esi+1064]
	adc edx, DWORD PTR [esi+1068]
	mov DWORD PTR [esi+1064], eax
	mov DWORD PTR [esi+1068], edx
	mov eax, DWORD PTR [esi+1832]
	mov edx, DWORD PTR [esi+1836]
	xor eax, DWORD PTR [esi+1064]
	xor edx, DWORD PTR [esi+1068]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1832], edx
	mov DWORD PTR [esi+1836], eax
	mov edx, DWORD PTR [esi+1832]
	mov eax, DWORD PTR [esi+1576]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1832]
	adc edx, DWORD PTR [esi+1836]
	add eax, DWORD PTR [esi+1576]
	adc edx, DWORD PTR [esi+1580]
	mov DWORD PTR [esi+1576], eax
	mov DWORD PTR [esi+1580], edx
	mov eax, DWORD PTR [esi+1320]
	mov edx, DWORD PTR [esi+1324]
	xor eax, DWORD PTR [esi+1576]
	xor edx, DWORD PTR [esi+1580]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1320], eax
	mov DWORD PTR [esi+1324], edx
	mov edx, DWORD PTR [esi+1440]
	mov eax, DWORD PTR [esi+1184]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1440]
	adc edx, DWORD PTR [esi+1444]
	add eax, DWORD PTR [esi+1184]
	adc edx, DWORD PTR [esi+1188]
	mov DWORD PTR [esi+1184], eax
	mov DWORD PTR [esi+1188], edx
	mov eax, DWORD PTR [esi+1952]
	mov edx, DWORD PTR [esi+1956]
	xor eax, DWORD PTR [esi+1184]
	xor edx, DWORD PTR [esi+1188]
	mov DWORD PTR [esi+1952], edx
	mov DWORD PTR [esi+1956], eax
	mov edx, DWORD PTR [esi+1952]
	mov eax, DWORD PTR [esi+1696]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1952]
	adc edx, DWORD PTR [esi+1956]
	add eax, DWORD PTR [esi+1696]
	adc edx, DWORD PTR [esi+1700]
	mov DWORD PTR [esi+1696], eax
	mov DWORD PTR [esi+1700], edx
	mov eax, DWORD PTR [esi+1440]
	mov edx, DWORD PTR [esi+1444]
	xor eax, DWORD PTR [esi+1696]
	xor edx, DWORD PTR [esi+1700]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1440], edx
	mov DWORD PTR [esi+1444], eax
	mov edx, DWORD PTR [esi+1440]
	mov eax, DWORD PTR [esi+1184]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1440]
	adc edx, DWORD PTR [esi+1444]
	add eax, DWORD PTR [esi+1184]
	adc edx, DWORD PTR [esi+1188]
	mov DWORD PTR [esi+1184], eax
	mov DWORD PTR [esi+1188], edx
	mov eax, DWORD PTR [esi+1952]
	mov edx, DWORD PTR [esi+1956]
	xor eax, DWORD PTR [esi+1184]
	xor edx, DWORD PTR [esi+1188]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1952], edx
	mov DWORD PTR [esi+1956], eax
	mov edx, DWORD PTR [esi+1952]
	mov eax, DWORD PTR [esi+1696]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1952]
	adc edx, DWORD PTR [esi+1956]
	add eax, DWORD PTR [esi+1696]
	adc edx, DWORD PTR [esi+1700]
	mov DWORD PTR [esi+1696], eax
	mov DWORD PTR [esi+1700], edx
	mov eax, DWORD PTR [esi+1440]
	mov edx, DWORD PTR [esi+1444]
	xor eax, DWORD PTR [esi+1696]
	xor edx, DWORD PTR [esi+1700]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1440], eax
	mov DWORD PTR [esi+1444], edx
	mov edx, DWORD PTR [esi+1448]
	mov eax, DWORD PTR [esi+1192]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1448]
	adc edx, DWORD PTR [esi+1452]
	add eax, DWORD PTR [esi+1192]
	adc edx, DWORD PTR [esi+1196]
	mov DWORD PTR [esi+1192], eax
	mov DWORD PTR [esi+1196], edx
	mov eax, DWORD PTR [esi+1960]
	mov edx, DWORD PTR [esi+1964]
	xor eax, DWORD PTR [esi+1192]
	xor edx, DWORD PTR [esi+1196]
	mov DWORD PTR [esi+1960], edx
	mov DWORD PTR [esi+1964], eax
	mov edx, DWORD PTR [esi+1960]
	mov eax, DWORD PTR [esi+1704]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1960]
	adc edx, DWORD PTR [esi+1964]
	add eax, DWORD PTR [esi+1704]
	adc edx, DWORD PTR [esi+1708]
	mov DWORD PTR [esi+1704], eax
	mov DWORD PTR [esi+1708], edx
	mov eax, DWORD PTR [esi+1448]
	mov edx, DWORD PTR [esi+1452]
	xor eax, DWORD PTR [esi+1704]
	xor edx, DWORD PTR [esi+1708]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1448], edx
	mov DWORD PTR [esi+1452], eax
	mov edx, DWORD PTR [esi+1448]
	mov eax, DWORD PTR [esi+1192]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1448]
	adc edx, DWORD PTR [esi+1452]
	add eax, DWORD PTR [esi+1192]
	adc edx, DWORD PTR [esi+1196]
	mov DWORD PTR [esi+1192], eax
	mov DWORD PTR [esi+1196], edx
	mov eax, DWORD PTR [esi+1960]
	mov edx, DWORD PTR [esi+1964]
	xor eax, DWORD PTR [esi+1192]
	xor edx, DWORD PTR [esi+1196]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1960], edx
	mov DWORD PTR [esi+1964], eax
	mov edx, DWORD PTR [esi+1960]
	mov eax, DWORD PTR [esi+1704]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1960]
	adc edx, DWORD PTR [esi+1964]
	add eax, DWORD PTR [esi+1704]
	adc edx, DWORD PTR [esi+1708]
	mov DWORD PTR [esi+1704], eax
	mov DWORD PTR [esi+1708], edx
	mov eax, DWORD PTR [esi+1448]
	mov edx, DWORD PTR [esi+1452]
	xor eax, DWORD PTR [esi+1704]
	xor edx, DWORD PTR [esi+1708]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1448], eax
	mov DWORD PTR [esi+1452], edx
	mov edx, DWORD PTR [esi+1320]
	mov eax, DWORD PTR [esi+1056]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1320]
	adc edx, DWORD PTR [esi+1324]
	add eax, DWORD PTR [esi+1056]
	adc edx, DWORD PTR [esi+1060]
	mov DWORD PTR [esi+1056], eax
	mov DWORD PTR [esi+1060], edx
	mov eax, DWORD PTR [esi+1960]
	mov edx, DWORD PTR [esi+1964]
	xor eax, DWORD PTR [esi+1056]
	xor edx, DWORD PTR [esi+1060]
	mov DWORD PTR [esi+1960], edx
	mov DWORD PTR [esi+1964], eax
	mov edx, DWORD PTR [esi+1960]
	mov eax, DWORD PTR [esi+1696]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1960]
	adc edx, DWORD PTR [esi+1964]
	add eax, DWORD PTR [esi+1696]
	adc edx, DWORD PTR [esi+1700]
	mov DWORD PTR [esi+1696], eax
	mov DWORD PTR [esi+1700], edx
	mov eax, DWORD PTR [esi+1320]
	mov edx, DWORD PTR [esi+1324]
	xor eax, DWORD PTR [esi+1696]
	xor edx, DWORD PTR [esi+1700]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1320], edx
	mov DWORD PTR [esi+1324], eax
	mov edx, DWORD PTR [esi+1320]
	mov eax, DWORD PTR [esi+1056]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1320]
	adc edx, DWORD PTR [esi+1324]
	add eax, DWORD PTR [esi+1056]
	adc edx, DWORD PTR [esi+1060]
	mov DWORD PTR [esi+1056], eax
	mov DWORD PTR [esi+1060], edx
	mov eax, DWORD PTR [esi+1960]
	mov edx, DWORD PTR [esi+1964]
	xor eax, DWORD PTR [esi+1056]
	xor edx, DWORD PTR [esi+1060]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1960], edx
	mov DWORD PTR [esi+1964], eax
	mov edx, DWORD PTR [esi+1960]
	mov eax, DWORD PTR [esi+1696]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1960]
	adc edx, DWORD PTR [esi+1964]
	add eax, DWORD PTR [esi+1696]
	adc edx, DWORD PTR [esi+1700]
	mov DWORD PTR [esi+1696], eax
	mov DWORD PTR [esi+1700], edx
	mov eax, DWORD PTR [esi+1320]
	mov edx, DWORD PTR [esi+1324]
	xor eax, DWORD PTR [esi+1696]
	xor edx, DWORD PTR [esi+1700]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1320], eax
	mov DWORD PTR [esi+1324], edx
	mov edx, DWORD PTR [esi+1440]
	mov eax, DWORD PTR [esi+1064]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1440]
	adc edx, DWORD PTR [esi+1444]
	add eax, DWORD PTR [esi+1064]
	adc edx, DWORD PTR [esi+1068]
	mov DWORD PTR [esi+1064], eax
	mov DWORD PTR [esi+1068], edx
	mov eax, DWORD PTR [esi+1824]
	mov edx, DWORD PTR [esi+1828]
	xor eax, DWORD PTR [esi+1064]
	xor edx, DWORD PTR [esi+1068]
	mov DWORD PTR [esi+1824], edx
	mov DWORD PTR [esi+1828], eax
	mov edx, DWORD PTR [esi+1824]
	mov eax, DWORD PTR [esi+1704]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1824]
	adc edx, DWORD PTR [esi+1828]
	add eax, DWORD PTR [esi+1704]
	adc edx, DWORD PTR [esi+1708]
	mov DWORD PTR [esi+1704], eax
	mov DWORD PTR [esi+1708], edx
	mov eax, DWORD PTR [esi+1440]
	mov edx, DWORD PTR [esi+1444]
	xor eax, DWORD PTR [esi+1704]
	xor edx, DWORD PTR [esi+1708]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1440], edx
	mov DWORD PTR [esi+1444], eax
	mov edx, DWORD PTR [esi+1440]
	mov eax, DWORD PTR [esi+1064]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1440]
	adc edx, DWORD PTR [esi+1444]
	add eax, DWORD PTR [esi+1064]
	adc edx, DWORD PTR [esi+1068]
	mov DWORD PTR [esi+1064], eax
	mov DWORD PTR [esi+1068], edx
	mov eax, DWORD PTR [esi+1824]
	mov edx, DWORD PTR [esi+1828]
	xor eax, DWORD PTR [esi+1064]
	xor edx, DWORD PTR [esi+1068]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1824], edx
	mov DWORD PTR [esi+1828], eax
	mov edx, DWORD PTR [esi+1824]
	mov eax, DWORD PTR [esi+1704]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1824]
	adc edx, DWORD PTR [esi+1828]
	add eax, DWORD PTR [esi+1704]
	adc edx, DWORD PTR [esi+1708]
	mov DWORD PTR [esi+1704], eax
	mov DWORD PTR [esi+1708], edx
	mov eax, DWORD PTR [esi+1440]
	mov edx, DWORD PTR [esi+1444]
	xor eax, DWORD PTR [esi+1704]
	xor edx, DWORD PTR [esi+1708]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1440], eax
	mov DWORD PTR [esi+1444], edx
	mov edx, DWORD PTR [esi+1448]
	mov eax, DWORD PTR [esi+1184]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1448]
	adc edx, DWORD PTR [esi+1452]
	add eax, DWORD PTR [esi+1184]
	adc edx, DWORD PTR [esi+1188]
	mov DWORD PTR [esi+1184], eax
	mov DWORD PTR [esi+1188], edx
	mov eax, DWORD PTR [esi+1832]
	mov edx, DWORD PTR [esi+1836]
	xor eax, DWORD PTR [esi+1184]
	xor edx, DWORD PTR [esi+1188]
	mov DWORD PTR [esi+1832], edx
	mov DWORD PTR [esi+1836], eax
	mov edx, DWORD PTR [esi+1832]
	mov eax, DWORD PTR [esi+1568]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1832]
	adc edx, DWORD PTR [esi+1836]
	add eax, DWORD PTR [esi+1568]
	adc edx, DWORD PTR [esi+1572]
	mov DWORD PTR [esi+1568], eax
	mov DWORD PTR [esi+1572], edx
	mov eax, DWORD PTR [esi+1448]
	mov edx, DWORD PTR [esi+1452]
	xor eax, DWORD PTR [esi+1568]
	xor edx, DWORD PTR [esi+1572]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1448], edx
	mov DWORD PTR [esi+1452], eax
	mov edx, DWORD PTR [esi+1448]
	mov eax, DWORD PTR [esi+1184]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1448]
	adc edx, DWORD PTR [esi+1452]
	add eax, DWORD PTR [esi+1184]
	adc edx, DWORD PTR [esi+1188]
	mov DWORD PTR [esi+1184], eax
	mov DWORD PTR [esi+1188], edx
	mov eax, DWORD PTR [esi+1832]
	mov edx, DWORD PTR [esi+1836]
	xor eax, DWORD PTR [esi+1184]
	xor edx, DWORD PTR [esi+1188]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1832], edx
	mov DWORD PTR [esi+1836], eax
	mov edx, DWORD PTR [esi+1832]
	mov eax, DWORD PTR [esi+1568]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1832]
	adc edx, DWORD PTR [esi+1836]
	add eax, DWORD PTR [esi+1568]
	adc edx, DWORD PTR [esi+1572]
	mov DWORD PTR [esi+1568], eax
	mov DWORD PTR [esi+1572], edx
	mov eax, DWORD PTR [esi+1448]
	mov edx, DWORD PTR [esi+1452]
	xor eax, DWORD PTR [esi+1568]
	xor edx, DWORD PTR [esi+1572]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1448], eax
	mov DWORD PTR [esi+1452], edx
	mov edx, DWORD PTR [esi+1312]
	mov eax, DWORD PTR [esi+1192]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1312]
	adc edx, DWORD PTR [esi+1316]
	add eax, DWORD PTR [esi+1192]
	adc edx, DWORD PTR [esi+1196]
	mov DWORD PTR [esi+1192], eax
	mov DWORD PTR [esi+1196], edx
	mov eax, DWORD PTR [esi+1952]
	mov edx, DWORD PTR [esi+1956]
	xor eax, DWORD PTR [esi+1192]
	xor edx, DWORD PTR [esi+1196]
	mov DWORD PTR [esi+1952], edx
	mov DWORD PTR [esi+1956], eax
	mov edx, DWORD PTR [esi+1952]
	mov eax, DWORD PTR [esi+1576]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1952]
	adc edx, DWORD PTR [esi+1956]
	add eax, DWORD PTR [esi+1576]
	adc edx, DWORD PTR [esi+1580]
	mov DWORD PTR [esi+1576], eax
	mov DWORD PTR [esi+1580], edx
	mov eax, DWORD PTR [esi+1312]
	mov edx, DWORD PTR [esi+1316]
	xor eax, DWORD PTR [esi+1576]
	xor edx, DWORD PTR [esi+1580]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1312], edx
	mov DWORD PTR [esi+1316], eax
	mov edx, DWORD PTR [esi+1312]
	mov eax, DWORD PTR [esi+1192]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1312]
	adc edx, DWORD PTR [esi+1316]
	add eax, DWORD PTR [esi+1192]
	adc edx, DWORD PTR [esi+1196]
	mov DWORD PTR [esi+1192], eax
	mov DWORD PTR [esi+1196], edx
	mov eax, DWORD PTR [esi+1952]
	mov edx, DWORD PTR [esi+1956]
	xor eax, DWORD PTR [esi+1192]
	xor edx, DWORD PTR [esi+1196]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1952], edx
	mov DWORD PTR [esi+1956], eax
	mov edx, DWORD PTR [esi+1952]
	mov eax, DWORD PTR [esi+1576]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1952]
	adc edx, DWORD PTR [esi+1956]
	add eax, DWORD PTR [esi+1576]
	adc edx, DWORD PTR [esi+1580]
	mov DWORD PTR [esi+1576], eax
	mov DWORD PTR [esi+1580], edx
	mov eax, DWORD PTR [esi+1312]
	mov edx, DWORD PTR [esi+1316]
	xor eax, DWORD PTR [esi+1576]
	xor edx, DWORD PTR [esi+1580]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1312], eax
	mov DWORD PTR [esi+1316], edx
	mov edx, DWORD PTR [esi+1328]
	mov eax, DWORD PTR [esi+1072]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1328]
	adc edx, DWORD PTR [esi+1332]
	add eax, DWORD PTR [esi+1072]
	adc edx, DWORD PTR [esi+1076]
	mov DWORD PTR [esi+1072], eax
	mov DWORD PTR [esi+1076], edx
	mov eax, DWORD PTR [esi+1840]
	mov edx, DWORD PTR [esi+1844]
	xor eax, DWORD PTR [esi+1072]
	xor edx, DWORD PTR [esi+1076]
	mov DWORD PTR [esi+1840], edx
	mov DWORD PTR [esi+1844], eax
	mov edx, DWORD PTR [esi+1840]
	mov eax, DWORD PTR [esi+1584]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1840]
	adc edx, DWORD PTR [esi+1844]
	add eax, DWORD PTR [esi+1584]
	adc edx, DWORD PTR [esi+1588]
	mov DWORD PTR [esi+1584], eax
	mov DWORD PTR [esi+1588], edx
	mov eax, DWORD PTR [esi+1328]
	mov edx, DWORD PTR [esi+1332]
	xor eax, DWORD PTR [esi+1584]
	xor edx, DWORD PTR [esi+1588]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1328], edx
	mov DWORD PTR [esi+1332], eax
	mov edx, DWORD PTR [esi+1328]
	mov eax, DWORD PTR [esi+1072]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1328]
	adc edx, DWORD PTR [esi+1332]
	add eax, DWORD PTR [esi+1072]
	adc edx, DWORD PTR [esi+1076]
	mov DWORD PTR [esi+1072], eax
	mov DWORD PTR [esi+1076], edx
	mov eax, DWORD PTR [esi+1840]
	mov edx, DWORD PTR [esi+1844]
	xor eax, DWORD PTR [esi+1072]
	xor edx, DWORD PTR [esi+1076]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1840], edx
	mov DWORD PTR [esi+1844], eax
	mov edx, DWORD PTR [esi+1840]
	mov eax, DWORD PTR [esi+1584]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1840]
	adc edx, DWORD PTR [esi+1844]
	add eax, DWORD PTR [esi+1584]
	adc edx, DWORD PTR [esi+1588]
	mov DWORD PTR [esi+1584], eax
	mov DWORD PTR [esi+1588], edx
	mov eax, DWORD PTR [esi+1328]
	mov edx, DWORD PTR [esi+1332]
	xor eax, DWORD PTR [esi+1584]
	xor edx, DWORD PTR [esi+1588]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1328], eax
	mov DWORD PTR [esi+1332], edx
	mov edx, DWORD PTR [esi+1336]
	mov eax, DWORD PTR [esi+1080]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1336]
	adc edx, DWORD PTR [esi+1340]
	add eax, DWORD PTR [esi+1080]
	adc edx, DWORD PTR [esi+1084]
	mov DWORD PTR [esi+1080], eax
	mov DWORD PTR [esi+1084], edx
	mov eax, DWORD PTR [esi+1848]
	mov edx, DWORD PTR [esi+1852]
	xor eax, DWORD PTR [esi+1080]
	xor edx, DWORD PTR [esi+1084]
	mov DWORD PTR [esi+1848], edx
	mov DWORD PTR [esi+1852], eax
	mov edx, DWORD PTR [esi+1848]
	mov eax, DWORD PTR [esi+1592]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1848]
	adc edx, DWORD PTR [esi+1852]
	add eax, DWORD PTR [esi+1592]
	adc edx, DWORD PTR [esi+1596]
	mov DWORD PTR [esi+1592], eax
	mov DWORD PTR [esi+1596], edx
	mov eax, DWORD PTR [esi+1336]
	mov edx, DWORD PTR [esi+1340]
	xor eax, DWORD PTR [esi+1592]
	xor edx, DWORD PTR [esi+1596]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1336], edx
	mov DWORD PTR [esi+1340], eax
	mov edx, DWORD PTR [esi+1336]
	mov eax, DWORD PTR [esi+1080]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1336]
	adc edx, DWORD PTR [esi+1340]
	add eax, DWORD PTR [esi+1080]
	adc edx, DWORD PTR [esi+1084]
	mov DWORD PTR [esi+1080], eax
	mov DWORD PTR [esi+1084], edx
	mov eax, DWORD PTR [esi+1848]
	mov edx, DWORD PTR [esi+1852]
	xor eax, DWORD PTR [esi+1080]
	xor edx, DWORD PTR [esi+1084]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1848], edx
	mov DWORD PTR [esi+1852], eax
	mov edx, DWORD PTR [esi+1848]
	mov eax, DWORD PTR [esi+1592]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1848]
	adc edx, DWORD PTR [esi+1852]
	add eax, DWORD PTR [esi+1592]
	adc edx, DWORD PTR [esi+1596]
	mov DWORD PTR [esi+1592], eax
	mov DWORD PTR [esi+1596], edx
	mov eax, DWORD PTR [esi+1336]
	mov edx, DWORD PTR [esi+1340]
	xor eax, DWORD PTR [esi+1592]
	xor edx, DWORD PTR [esi+1596]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1336], eax
	mov DWORD PTR [esi+1340], edx
	mov edx, DWORD PTR [esi+1456]
	mov eax, DWORD PTR [esi+1200]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1456]
	adc edx, DWORD PTR [esi+1460]
	add eax, DWORD PTR [esi+1200]
	adc edx, DWORD PTR [esi+1204]
	mov DWORD PTR [esi+1200], eax
	mov DWORD PTR [esi+1204], edx
	mov eax, DWORD PTR [esi+1968]
	mov edx, DWORD PTR [esi+1972]
	xor eax, DWORD PTR [esi+1200]
	xor edx, DWORD PTR [esi+1204]
	mov DWORD PTR [esi+1968], edx
	mov DWORD PTR [esi+1972], eax
	mov edx, DWORD PTR [esi+1968]
	mov eax, DWORD PTR [esi+1712]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1968]
	adc edx, DWORD PTR [esi+1972]
	add eax, DWORD PTR [esi+1712]
	adc edx, DWORD PTR [esi+1716]
	mov DWORD PTR [esi+1712], eax
	mov DWORD PTR [esi+1716], edx
	mov eax, DWORD PTR [esi+1456]
	mov edx, DWORD PTR [esi+1460]
	xor eax, DWORD PTR [esi+1712]
	xor edx, DWORD PTR [esi+1716]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1456], edx
	mov DWORD PTR [esi+1460], eax
	mov edx, DWORD PTR [esi+1456]
	mov eax, DWORD PTR [esi+1200]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1456]
	adc edx, DWORD PTR [esi+1460]
	add eax, DWORD PTR [esi+1200]
	adc edx, DWORD PTR [esi+1204]
	mov DWORD PTR [esi+1200], eax
	mov DWORD PTR [esi+1204], edx
	mov eax, DWORD PTR [esi+1968]
	mov edx, DWORD PTR [esi+1972]
	xor eax, DWORD PTR [esi+1200]
	xor edx, DWORD PTR [esi+1204]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1968], edx
	mov DWORD PTR [esi+1972], eax
	mov edx, DWORD PTR [esi+1968]
	mov eax, DWORD PTR [esi+1712]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1968]
	adc edx, DWORD PTR [esi+1972]
	add eax, DWORD PTR [esi+1712]
	adc edx, DWORD PTR [esi+1716]
	mov DWORD PTR [esi+1712], eax
	mov DWORD PTR [esi+1716], edx
	mov eax, DWORD PTR [esi+1456]
	mov edx, DWORD PTR [esi+1460]
	xor eax, DWORD PTR [esi+1712]
	xor edx, DWORD PTR [esi+1716]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1456], eax
	mov DWORD PTR [esi+1460], edx
	mov edx, DWORD PTR [esi+1464]
	mov eax, DWORD PTR [esi+1208]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1464]
	adc edx, DWORD PTR [esi+1468]
	add eax, DWORD PTR [esi+1208]
	adc edx, DWORD PTR [esi+1212]
	mov DWORD PTR [esi+1208], eax
	mov DWORD PTR [esi+1212], edx
	mov eax, DWORD PTR [esi+1976]
	mov edx, DWORD PTR [esi+1980]
	xor eax, DWORD PTR [esi+1208]
	xor edx, DWORD PTR [esi+1212]
	mov DWORD PTR [esi+1976], edx
	mov DWORD PTR [esi+1980], eax
	mov edx, DWORD PTR [esi+1976]
	mov eax, DWORD PTR [esi+1720]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1976]
	adc edx, DWORD PTR [esi+1980]
	add eax, DWORD PTR [esi+1720]
	adc edx, DWORD PTR [esi+1724]
	mov DWORD PTR [esi+1720], eax
	mov DWORD PTR [esi+1724], edx
	mov eax, DWORD PTR [esi+1464]
	mov edx, DWORD PTR [esi+1468]
	xor eax, DWORD PTR [esi+1720]
	xor edx, DWORD PTR [esi+1724]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1464], edx
	mov DWORD PTR [esi+1468], eax
	mov edx, DWORD PTR [esi+1464]
	mov eax, DWORD PTR [esi+1208]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1464]
	adc edx, DWORD PTR [esi+1468]
	add eax, DWORD PTR [esi+1208]
	adc edx, DWORD PTR [esi+1212]
	mov DWORD PTR [esi+1208], eax
	mov DWORD PTR [esi+1212], edx
	mov eax, DWORD PTR [esi+1976]
	mov edx, DWORD PTR [esi+1980]
	xor eax, DWORD PTR [esi+1208]
	xor edx, DWORD PTR [esi+1212]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1976], edx
	mov DWORD PTR [esi+1980], eax
	mov edx, DWORD PTR [esi+1976]
	mov eax, DWORD PTR [esi+1720]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1976]
	adc edx, DWORD PTR [esi+1980]
	add eax, DWORD PTR [esi+1720]
	adc edx, DWORD PTR [esi+1724]
	mov DWORD PTR [esi+1720], eax
	mov DWORD PTR [esi+1724], edx
	mov eax, DWORD PTR [esi+1464]
	mov edx, DWORD PTR [esi+1468]
	xor eax, DWORD PTR [esi+1720]
	xor edx, DWORD PTR [esi+1724]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1464], eax
	mov DWORD PTR [esi+1468], edx
	mov edx, DWORD PTR [esi+1336]
	mov eax, DWORD PTR [esi+1072]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1336]
	adc edx, DWORD PTR [esi+1340]
	add eax, DWORD PTR [esi+1072]
	adc edx, DWORD PTR [esi+1076]
	mov DWORD PTR [esi+1072], eax
	mov DWORD PTR [esi+1076], edx
	mov eax, DWORD PTR [esi+1976]
	mov edx, DWORD PTR [esi+1980]
	xor eax, DWORD PTR [esi+1072]
	xor edx, DWORD PTR [esi+1076]
	mov DWORD PTR [esi+1976], edx
	mov DWORD PTR [esi+1980], eax
	mov edx, DWORD PTR [esi+1976]
	mov eax, DWORD PTR [esi+1712]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1976]
	adc edx, DWORD PTR [esi+1980]
	add eax, DWORD PTR [esi+1712]
	adc edx, DWORD PTR [esi+1716]
	mov DWORD PTR [esi+1712], eax
	mov DWORD PTR [esi+1716], edx
	mov eax, DWORD PTR [esi+1336]
	mov edx, DWORD PTR [esi+1340]
	xor eax, DWORD PTR [esi+1712]
	xor edx, DWORD PTR [esi+1716]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1336], edx
	mov DWORD PTR [esi+1340], eax
	mov edx, DWORD PTR [esi+1336]
	mov eax, DWORD PTR [esi+1072]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1336]
	adc edx, DWORD PTR [esi+1340]
	add eax, DWORD PTR [esi+1072]
	adc edx, DWORD PTR [esi+1076]
	mov DWORD PTR [esi+1072], eax
	mov DWORD PTR [esi+1076], edx
	mov eax, DWORD PTR [esi+1976]
	mov edx, DWORD PTR [esi+1980]
	xor eax, DWORD PTR [esi+1072]
	xor edx, DWORD PTR [esi+1076]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1976], edx
	mov DWORD PTR [esi+1980], eax
	mov edx, DWORD PTR [esi+1976]
	mov eax, DWORD PTR [esi+1712]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1976]
	adc edx, DWORD PTR [esi+1980]
	add eax, DWORD PTR [esi+1712]
	adc edx, DWORD PTR [esi+1716]
	mov DWORD PTR [esi+1712], eax
	mov DWORD PTR [esi+1716], edx
	mov eax, DWORD PTR [esi+1336]
	mov edx, DWORD PTR [esi+1340]
	xor eax, DWORD PTR [esi+1712]
	xor edx, DWORD PTR [esi+1716]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1336], eax
	mov DWORD PTR [esi+1340], edx
	mov edx, DWORD PTR [esi+1456]
	mov eax, DWORD PTR [esi+1080]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1456]
	adc edx, DWORD PTR [esi+1460]
	add eax, DWORD PTR [esi+1080]
	adc edx, DWORD PTR [esi+1084]
	mov DWORD PTR [esi+1080], eax
	mov DWORD PTR [esi+1084], edx
	mov eax, DWORD PTR [esi+1840]
	mov edx, DWORD PTR [esi+1844]
	xor eax, DWORD PTR [esi+1080]
	xor edx, DWORD PTR [esi+1084]
	mov DWORD PTR [esi+1840], edx
	mov DWORD PTR [esi+1844], eax
	mov edx, DWORD PTR [esi+1840]
	mov eax, DWORD PTR [esi+1720]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1840]
	adc edx, DWORD PTR [esi+1844]
	add eax, DWORD PTR [esi+1720]
	adc edx, DWORD PTR [esi+1724]
	mov DWORD PTR [esi+1720], eax
	mov DWORD PTR [esi+1724], edx
	mov eax, DWORD PTR [esi+1456]
	mov edx, DWORD PTR [esi+1460]
	xor eax, DWORD PTR [esi+1720]
	xor edx, DWORD PTR [esi+1724]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1456], edx
	mov DWORD PTR [esi+1460], eax
	mov edx, DWORD PTR [esi+1456]
	mov eax, DWORD PTR [esi+1080]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1456]
	adc edx, DWORD PTR [esi+1460]
	add eax, DWORD PTR [esi+1080]
	adc edx, DWORD PTR [esi+1084]
	mov DWORD PTR [esi+1080], eax
	mov DWORD PTR [esi+1084], edx
	mov eax, DWORD PTR [esi+1840]
	mov edx, DWORD PTR [esi+1844]
	xor eax, DWORD PTR [esi+1080]
	xor edx, DWORD PTR [esi+1084]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1840], edx
	mov DWORD PTR [esi+1844], eax
	mov edx, DWORD PTR [esi+1840]
	mov eax, DWORD PTR [esi+1720]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1840]
	adc edx, DWORD PTR [esi+1844]
	add eax, DWORD PTR [esi+1720]
	adc edx, DWORD PTR [esi+1724]
	mov DWORD PTR [esi+1720], eax
	mov DWORD PTR [esi+1724], edx
	mov eax, DWORD PTR [esi+1456]
	mov edx, DWORD PTR [esi+1460]
	xor eax, DWORD PTR [esi+1720]
	xor edx, DWORD PTR [esi+1724]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1456], eax
	mov DWORD PTR [esi+1460], edx
	mov edx, DWORD PTR [esi+1464]
	mov eax, DWORD PTR [esi+1200]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1464]
	adc edx, DWORD PTR [esi+1468]
	add eax, DWORD PTR [esi+1200]
	adc edx, DWORD PTR [esi+1204]
	mov DWORD PTR [esi+1200], eax
	mov DWORD PTR [esi+1204], edx
	mov eax, DWORD PTR [esi+1848]
	mov edx, DWORD PTR [esi+1852]
	xor eax, DWORD PTR [esi+1200]
	xor edx, DWORD PTR [esi+1204]
	mov DWORD PTR [esi+1848], edx
	mov DWORD PTR [esi+1852], eax
	mov edx, DWORD PTR [esi+1848]
	mov eax, DWORD PTR [esi+1584]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1848]
	adc edx, DWORD PTR [esi+1852]
	add eax, DWORD PTR [esi+1584]
	adc edx, DWORD PTR [esi+1588]
	mov DWORD PTR [esi+1584], eax
	mov DWORD PTR [esi+1588], edx
	mov eax, DWORD PTR [esi+1464]
	mov edx, DWORD PTR [esi+1468]
	xor eax, DWORD PTR [esi+1584]
	xor edx, DWORD PTR [esi+1588]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1464], edx
	mov DWORD PTR [esi+1468], eax
	mov edx, DWORD PTR [esi+1464]
	mov eax, DWORD PTR [esi+1200]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1464]
	adc edx, DWORD PTR [esi+1468]
	add eax, DWORD PTR [esi+1200]
	adc edx, DWORD PTR [esi+1204]
	mov DWORD PTR [esi+1200], eax
	mov DWORD PTR [esi+1204], edx
	mov eax, DWORD PTR [esi+1848]
	mov edx, DWORD PTR [esi+1852]
	xor eax, DWORD PTR [esi+1200]
	xor edx, DWORD PTR [esi+1204]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1848], edx
	mov DWORD PTR [esi+1852], eax
	mov edx, DWORD PTR [esi+1848]
	mov eax, DWORD PTR [esi+1584]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1848]
	adc edx, DWORD PTR [esi+1852]
	add eax, DWORD PTR [esi+1584]
	adc edx, DWORD PTR [esi+1588]
	mov DWORD PTR [esi+1584], eax
	mov DWORD PTR [esi+1588], edx
	mov eax, DWORD PTR [esi+1464]
	mov edx, DWORD PTR [esi+1468]
	xor eax, DWORD PTR [esi+1584]
	xor edx, DWORD PTR [esi+1588]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1464], eax
	mov DWORD PTR [esi+1468], edx
	mov edx, DWORD PTR [esi+1328]
	mov eax, DWORD PTR [esi+1208]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1328]
	adc edx, DWORD PTR [esi+1332]
	add eax, DWORD PTR [esi+1208]
	adc edx, DWORD PTR [esi+1212]
	mov DWORD PTR [esi+1208], eax
	mov DWORD PTR [esi+1212], edx
	mov eax, DWORD PTR [esi+1968]
	mov edx, DWORD PTR [esi+1972]
	xor eax, DWORD PTR [esi+1208]
	xor edx, DWORD PTR [esi+1212]
	mov DWORD PTR [esi+1968], edx
	mov DWORD PTR [esi+1972], eax
	mov edx, DWORD PTR [esi+1968]
	mov eax, DWORD PTR [esi+1592]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1968]
	adc edx, DWORD PTR [esi+1972]
	add eax, DWORD PTR [esi+1592]
	adc edx, DWORD PTR [esi+1596]
	mov DWORD PTR [esi+1592], eax
	mov DWORD PTR [esi+1596], edx
	mov eax, DWORD PTR [esi+1328]
	mov edx, DWORD PTR [esi+1332]
	xor eax, DWORD PTR [esi+1592]
	xor edx, DWORD PTR [esi+1596]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1328], edx
	mov DWORD PTR [esi+1332], eax
	mov edx, DWORD PTR [esi+1328]
	mov eax, DWORD PTR [esi+1208]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1328]
	adc edx, DWORD PTR [esi+1332]
	add eax, DWORD PTR [esi+1208]
	adc edx, DWORD PTR [esi+1212]
	mov DWORD PTR [esi+1208], eax
	mov DWORD PTR [esi+1212], edx
	mov eax, DWORD PTR [esi+1968]
	mov edx, DWORD PTR [esi+1972]
	xor eax, DWORD PTR [esi+1208]
	xor edx, DWORD PTR [esi+1212]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1968], edx
	mov DWORD PTR [esi+1972], eax
	mov edx, DWORD PTR [esi+1968]
	mov eax, DWORD PTR [esi+1592]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1968]
	adc edx, DWORD PTR [esi+1972]
	add eax, DWORD PTR [esi+1592]
	adc edx, DWORD PTR [esi+1596]
	mov DWORD PTR [esi+1592], eax
	mov DWORD PTR [esi+1596], edx
	mov eax, DWORD PTR [esi+1328]
	mov edx, DWORD PTR [esi+1332]
	xor eax, DWORD PTR [esi+1592]
	xor edx, DWORD PTR [esi+1596]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1328], eax
	mov DWORD PTR [esi+1332], edx
	mov edx, DWORD PTR [esi+1344]
	mov eax, DWORD PTR [esi+1088]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1344]
	adc edx, DWORD PTR [esi+1348]
	add eax, DWORD PTR [esi+1088]
	adc edx, DWORD PTR [esi+1092]
	mov DWORD PTR [esi+1088], eax
	mov DWORD PTR [esi+1092], edx
	mov eax, DWORD PTR [esi+1856]
	mov edx, DWORD PTR [esi+1860]
	xor eax, DWORD PTR [esi+1088]
	xor edx, DWORD PTR [esi+1092]
	mov DWORD PTR [esi+1856], edx
	mov DWORD PTR [esi+1860], eax
	mov edx, DWORD PTR [esi+1856]
	mov eax, DWORD PTR [esi+1600]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1856]
	adc edx, DWORD PTR [esi+1860]
	add eax, DWORD PTR [esi+1600]
	adc edx, DWORD PTR [esi+1604]
	mov DWORD PTR [esi+1600], eax
	mov DWORD PTR [esi+1604], edx
	mov eax, DWORD PTR [esi+1344]
	mov edx, DWORD PTR [esi+1348]
	xor eax, DWORD PTR [esi+1600]
	xor edx, DWORD PTR [esi+1604]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1344], edx
	mov DWORD PTR [esi+1348], eax
	mov edx, DWORD PTR [esi+1344]
	mov eax, DWORD PTR [esi+1088]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1344]
	adc edx, DWORD PTR [esi+1348]
	add eax, DWORD PTR [esi+1088]
	adc edx, DWORD PTR [esi+1092]
	mov DWORD PTR [esi+1088], eax
	mov DWORD PTR [esi+1092], edx
	mov eax, DWORD PTR [esi+1856]
	mov edx, DWORD PTR [esi+1860]
	xor eax, DWORD PTR [esi+1088]
	xor edx, DWORD PTR [esi+1092]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1856], edx
	mov DWORD PTR [esi+1860], eax
	mov edx, DWORD PTR [esi+1856]
	mov eax, DWORD PTR [esi+1600]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1856]
	adc edx, DWORD PTR [esi+1860]
	add eax, DWORD PTR [esi+1600]
	adc edx, DWORD PTR [esi+1604]
	mov DWORD PTR [esi+1600], eax
	mov DWORD PTR [esi+1604], edx
	mov eax, DWORD PTR [esi+1344]
	mov edx, DWORD PTR [esi+1348]
	xor eax, DWORD PTR [esi+1600]
	xor edx, DWORD PTR [esi+1604]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1344], eax
	mov DWORD PTR [esi+1348], edx
	mov edx, DWORD PTR [esi+1352]
	mov eax, DWORD PTR [esi+1096]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1352]
	adc edx, DWORD PTR [esi+1356]
	add eax, DWORD PTR [esi+1096]
	adc edx, DWORD PTR [esi+1100]
	mov DWORD PTR [esi+1096], eax
	mov DWORD PTR [esi+1100], edx
	mov eax, DWORD PTR [esi+1864]
	mov edx, DWORD PTR [esi+1868]
	xor eax, DWORD PTR [esi+1096]
	xor edx, DWORD PTR [esi+1100]
	mov DWORD PTR [esi+1864], edx
	mov DWORD PTR [esi+1868], eax
	mov edx, DWORD PTR [esi+1864]
	mov eax, DWORD PTR [esi+1608]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1864]
	adc edx, DWORD PTR [esi+1868]
	add eax, DWORD PTR [esi+1608]
	adc edx, DWORD PTR [esi+1612]
	mov DWORD PTR [esi+1608], eax
	mov DWORD PTR [esi+1612], edx
	mov eax, DWORD PTR [esi+1352]
	mov edx, DWORD PTR [esi+1356]
	xor eax, DWORD PTR [esi+1608]
	xor edx, DWORD PTR [esi+1612]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1352], edx
	mov DWORD PTR [esi+1356], eax
	mov edx, DWORD PTR [esi+1352]
	mov eax, DWORD PTR [esi+1096]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1352]
	adc edx, DWORD PTR [esi+1356]
	add eax, DWORD PTR [esi+1096]
	adc edx, DWORD PTR [esi+1100]
	mov DWORD PTR [esi+1096], eax
	mov DWORD PTR [esi+1100], edx
	mov eax, DWORD PTR [esi+1864]
	mov edx, DWORD PTR [esi+1868]
	xor eax, DWORD PTR [esi+1096]
	xor edx, DWORD PTR [esi+1100]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1864], edx
	mov DWORD PTR [esi+1868], eax
	mov edx, DWORD PTR [esi+1864]
	mov eax, DWORD PTR [esi+1608]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1864]
	adc edx, DWORD PTR [esi+1868]
	add eax, DWORD PTR [esi+1608]
	adc edx, DWORD PTR [esi+1612]
	mov DWORD PTR [esi+1608], eax
	mov DWORD PTR [esi+1612], edx
	mov eax, DWORD PTR [esi+1352]
	mov edx, DWORD PTR [esi+1356]
	xor eax, DWORD PTR [esi+1608]
	xor edx, DWORD PTR [esi+1612]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1352], eax
	mov DWORD PTR [esi+1356], edx
	mov edx, DWORD PTR [esi+1472]
	mov eax, DWORD PTR [esi+1216]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1472]
	adc edx, DWORD PTR [esi+1476]
	add eax, DWORD PTR [esi+1216]
	adc edx, DWORD PTR [esi+1220]
	mov DWORD PTR [esi+1216], eax
	mov DWORD PTR [esi+1220], edx
	mov eax, DWORD PTR [esi+1984]
	mov edx, DWORD PTR [esi+1988]
	xor eax, DWORD PTR [esi+1216]
	xor edx, DWORD PTR [esi+1220]
	mov DWORD PTR [esi+1984], edx
	mov DWORD PTR [esi+1988], eax
	mov edx, DWORD PTR [esi+1984]
	mov eax, DWORD PTR [esi+1728]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1984]
	adc edx, DWORD PTR [esi+1988]
	add eax, DWORD PTR [esi+1728]
	adc edx, DWORD PTR [esi+1732]
	mov DWORD PTR [esi+1728], eax
	mov DWORD PTR [esi+1732], edx
	mov eax, DWORD PTR [esi+1472]
	mov edx, DWORD PTR [esi+1476]
	xor eax, DWORD PTR [esi+1728]
	xor edx, DWORD PTR [esi+1732]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1472], edx
	mov DWORD PTR [esi+1476], eax
	mov edx, DWORD PTR [esi+1472]
	mov eax, DWORD PTR [esi+1216]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1472]
	adc edx, DWORD PTR [esi+1476]
	add eax, DWORD PTR [esi+1216]
	adc edx, DWORD PTR [esi+1220]
	mov DWORD PTR [esi+1216], eax
	mov DWORD PTR [esi+1220], edx
	mov eax, DWORD PTR [esi+1984]
	mov edx, DWORD PTR [esi+1988]
	xor eax, DWORD PTR [esi+1216]
	xor edx, DWORD PTR [esi+1220]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1984], edx
	mov DWORD PTR [esi+1988], eax
	mov edx, DWORD PTR [esi+1984]
	mov eax, DWORD PTR [esi+1728]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1984]
	adc edx, DWORD PTR [esi+1988]
	add eax, DWORD PTR [esi+1728]
	adc edx, DWORD PTR [esi+1732]
	mov DWORD PTR [esi+1728], eax
	mov DWORD PTR [esi+1732], edx
	mov eax, DWORD PTR [esi+1472]
	mov edx, DWORD PTR [esi+1476]
	xor eax, DWORD PTR [esi+1728]
	xor edx, DWORD PTR [esi+1732]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1472], eax
	mov DWORD PTR [esi+1476], edx
	mov edx, DWORD PTR [esi+1480]
	mov eax, DWORD PTR [esi+1224]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1480]
	adc edx, DWORD PTR [esi+1484]
	add eax, DWORD PTR [esi+1224]
	adc edx, DWORD PTR [esi+1228]
	mov DWORD PTR [esi+1224], eax
	mov DWORD PTR [esi+1228], edx
	mov eax, DWORD PTR [esi+1992]
	mov edx, DWORD PTR [esi+1996]
	xor eax, DWORD PTR [esi+1224]
	xor edx, DWORD PTR [esi+1228]
	mov DWORD PTR [esi+1992], edx
	mov DWORD PTR [esi+1996], eax
	mov edx, DWORD PTR [esi+1992]
	mov eax, DWORD PTR [esi+1736]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1992]
	adc edx, DWORD PTR [esi+1996]
	add eax, DWORD PTR [esi+1736]
	adc edx, DWORD PTR [esi+1740]
	mov DWORD PTR [esi+1736], eax
	mov DWORD PTR [esi+1740], edx
	mov eax, DWORD PTR [esi+1480]
	mov edx, DWORD PTR [esi+1484]
	xor eax, DWORD PTR [esi+1736]
	xor edx, DWORD PTR [esi+1740]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1480], edx
	mov DWORD PTR [esi+1484], eax
	mov edx, DWORD PTR [esi+1480]
	mov eax, DWORD PTR [esi+1224]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1480]
	adc edx, DWORD PTR [esi+1484]
	add eax, DWORD PTR [esi+1224]
	adc edx, DWORD PTR [esi+1228]
	mov DWORD PTR [esi+1224], eax
	mov DWORD PTR [esi+1228], edx
	mov eax, DWORD PTR [esi+1992]
	mov edx, DWORD PTR [esi+1996]
	xor eax, DWORD PTR [esi+1224]
	xor edx, DWORD PTR [esi+1228]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1992], edx
	mov DWORD PTR [esi+1996], eax
	mov edx, DWORD PTR [esi+1992]
	mov eax, DWORD PTR [esi+1736]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1992]
	adc edx, DWORD PTR [esi+1996]
	add eax, DWORD PTR [esi+1736]
	adc edx, DWORD PTR [esi+1740]
	mov DWORD PTR [esi+1736], eax
	mov DWORD PTR [esi+1740], edx
	mov eax, DWORD PTR [esi+1480]
	mov edx, DWORD PTR [esi+1484]
	xor eax, DWORD PTR [esi+1736]
	xor edx, DWORD PTR [esi+1740]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1480], eax
	mov DWORD PTR [esi+1484], edx
	mov edx, DWORD PTR [esi+1352]
	mov eax, DWORD PTR [esi+1088]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1352]
	adc edx, DWORD PTR [esi+1356]
	add eax, DWORD PTR [esi+1088]
	adc edx, DWORD PTR [esi+1092]
	mov DWORD PTR [esi+1088], eax
	mov DWORD PTR [esi+1092], edx
	mov eax, DWORD PTR [esi+1992]
	mov edx, DWORD PTR [esi+1996]
	xor eax, DWORD PTR [esi+1088]
	xor edx, DWORD PTR [esi+1092]
	mov DWORD PTR [esi+1992], edx
	mov DWORD PTR [esi+1996], eax
	mov edx, DWORD PTR [esi+1992]
	mov eax, DWORD PTR [esi+1728]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1992]
	adc edx, DWORD PTR [esi+1996]
	add eax, DWORD PTR [esi+1728]
	adc edx, DWORD PTR [esi+1732]
	mov DWORD PTR [esi+1728], eax
	mov DWORD PTR [esi+1732], edx
	mov eax, DWORD PTR [esi+1352]
	mov edx, DWORD PTR [esi+1356]
	xor eax, DWORD PTR [esi+1728]
	xor edx, DWORD PTR [esi+1732]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1352], edx
	mov DWORD PTR [esi+1356], eax
	mov edx, DWORD PTR [esi+1352]
	mov eax, DWORD PTR [esi+1088]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1352]
	adc edx, DWORD PTR [esi+1356]
	add eax, DWORD PTR [esi+1088]
	adc edx, DWORD PTR [esi+1092]
	mov DWORD PTR [esi+1088], eax
	mov DWORD PTR [esi+1092], edx
	mov eax, DWORD PTR [esi+1992]
	mov edx, DWORD PTR [esi+1996]
	xor eax, DWORD PTR [esi+1088]
	xor edx, DWORD PTR [esi+1092]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1992], edx
	mov DWORD PTR [esi+1996], eax
	mov edx, DWORD PTR [esi+1992]
	mov eax, DWORD PTR [esi+1728]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1992]
	adc edx, DWORD PTR [esi+1996]
	add eax, DWORD PTR [esi+1728]
	adc edx, DWORD PTR [esi+1732]
	mov DWORD PTR [esi+1728], eax
	mov DWORD PTR [esi+1732], edx
	mov eax, DWORD PTR [esi+1352]
	mov edx, DWORD PTR [esi+1356]
	xor eax, DWORD PTR [esi+1728]
	xor edx, DWORD PTR [esi+1732]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1352], eax
	mov DWORD PTR [esi+1356], edx
	mov edx, DWORD PTR [esi+1472]
	mov eax, DWORD PTR [esi+1096]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1472]
	adc edx, DWORD PTR [esi+1476]
	add eax, DWORD PTR [esi+1096]
	adc edx, DWORD PTR [esi+1100]
	mov DWORD PTR [esi+1096], eax
	mov DWORD PTR [esi+1100], edx
	mov eax, DWORD PTR [esi+1856]
	mov edx, DWORD PTR [esi+1860]
	xor eax, DWORD PTR [esi+1096]
	xor edx, DWORD PTR [esi+1100]
	mov DWORD PTR [esi+1856], edx
	mov DWORD PTR [esi+1860], eax
	mov edx, DWORD PTR [esi+1856]
	mov eax, DWORD PTR [esi+1736]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1856]
	adc edx, DWORD PTR [esi+1860]
	add eax, DWORD PTR [esi+1736]
	adc edx, DWORD PTR [esi+1740]
	mov DWORD PTR [esi+1736], eax
	mov DWORD PTR [esi+1740], edx
	mov eax, DWORD PTR [esi+1472]
	mov edx, DWORD PTR [esi+1476]
	xor eax, DWORD PTR [esi+1736]
	xor edx, DWORD PTR [esi+1740]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1472], edx
	mov DWORD PTR [esi+1476], eax
	mov edx, DWORD PTR [esi+1472]
	mov eax, DWORD PTR [esi+1096]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1472]
	adc edx, DWORD PTR [esi+1476]
	add eax, DWORD PTR [esi+1096]
	adc edx, DWORD PTR [esi+1100]
	mov DWORD PTR [esi+1096], eax
	mov DWORD PTR [esi+1100], edx
	mov eax, DWORD PTR [esi+1856]
	mov edx, DWORD PTR [esi+1860]
	xor eax, DWORD PTR [esi+1096]
	xor edx, DWORD PTR [esi+1100]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1856], edx
	mov DWORD PTR [esi+1860], eax
	mov edx, DWORD PTR [esi+1856]
	mov eax, DWORD PTR [esi+1736]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1856]
	adc edx, DWORD PTR [esi+1860]
	add eax, DWORD PTR [esi+1736]
	adc edx, DWORD PTR [esi+1740]
	mov DWORD PTR [esi+1736], eax
	mov DWORD PTR [esi+1740], edx
	mov eax, DWORD PTR [esi+1472]
	mov edx, DWORD PTR [esi+1476]
	xor eax, DWORD PTR [esi+1736]
	xor edx, DWORD PTR [esi+1740]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1472], eax
	mov DWORD PTR [esi+1476], edx
	mov edx, DWORD PTR [esi+1480]
	mov eax, DWORD PTR [esi+1216]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1480]
	adc edx, DWORD PTR [esi+1484]
	add eax, DWORD PTR [esi+1216]
	adc edx, DWORD PTR [esi+1220]
	mov DWORD PTR [esi+1216], eax
	mov DWORD PTR [esi+1220], edx
	mov eax, DWORD PTR [esi+1864]
	mov edx, DWORD PTR [esi+1868]
	xor eax, DWORD PTR [esi+1216]
	xor edx, DWORD PTR [esi+1220]
	mov DWORD PTR [esi+1864], edx
	mov DWORD PTR [esi+1868], eax
	mov edx, DWORD PTR [esi+1864]
	mov eax, DWORD PTR [esi+1600]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1864]
	adc edx, DWORD PTR [esi+1868]
	add eax, DWORD PTR [esi+1600]
	adc edx, DWORD PTR [esi+1604]
	mov DWORD PTR [esi+1600], eax
	mov DWORD PTR [esi+1604], edx
	mov eax, DWORD PTR [esi+1480]
	mov edx, DWORD PTR [esi+1484]
	xor eax, DWORD PTR [esi+1600]
	xor edx, DWORD PTR [esi+1604]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1480], edx
	mov DWORD PTR [esi+1484], eax
	mov edx, DWORD PTR [esi+1480]
	mov eax, DWORD PTR [esi+1216]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1480]
	adc edx, DWORD PTR [esi+1484]
	add eax, DWORD PTR [esi+1216]
	adc edx, DWORD PTR [esi+1220]
	mov DWORD PTR [esi+1216], eax
	mov DWORD PTR [esi+1220], edx
	mov eax, DWORD PTR [esi+1864]
	mov edx, DWORD PTR [esi+1868]
	xor eax, DWORD PTR [esi+1216]
	xor edx, DWORD PTR [esi+1220]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1864], edx
	mov DWORD PTR [esi+1868], eax
	mov edx, DWORD PTR [esi+1864]
	mov eax, DWORD PTR [esi+1600]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1864]
	adc edx, DWORD PTR [esi+1868]
	add eax, DWORD PTR [esi+1600]
	adc edx, DWORD PTR [esi+1604]
	mov DWORD PTR [esi+1600], eax
	mov DWORD PTR [esi+1604], edx
	mov eax, DWORD PTR [esi+1480]
	mov edx, DWORD PTR [esi+1484]
	xor eax, DWORD PTR [esi+1600]
	xor edx, DWORD PTR [esi+1604]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1480], eax
	mov DWORD PTR [esi+1484], edx
	mov edx, DWORD PTR [esi+1344]
	mov eax, DWORD PTR [esi+1224]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1344]
	adc edx, DWORD PTR [esi+1348]
	add eax, DWORD PTR [esi+1224]
	adc edx, DWORD PTR [esi+1228]
	mov DWORD PTR [esi+1224], eax
	mov DWORD PTR [esi+1228], edx
	mov eax, DWORD PTR [esi+1984]
	mov edx, DWORD PTR [esi+1988]
	xor eax, DWORD PTR [esi+1224]
	xor edx, DWORD PTR [esi+1228]
	mov DWORD PTR [esi+1984], edx
	mov DWORD PTR [esi+1988], eax
	mov edx, DWORD PTR [esi+1984]
	mov eax, DWORD PTR [esi+1608]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1984]
	adc edx, DWORD PTR [esi+1988]
	add eax, DWORD PTR [esi+1608]
	adc edx, DWORD PTR [esi+1612]
	mov DWORD PTR [esi+1608], eax
	mov DWORD PTR [esi+1612], edx
	mov eax, DWORD PTR [esi+1344]
	mov edx, DWORD PTR [esi+1348]
	xor eax, DWORD PTR [esi+1608]
	xor edx, DWORD PTR [esi+1612]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1344], edx
	mov DWORD PTR [esi+1348], eax
	mov edx, DWORD PTR [esi+1344]
	mov eax, DWORD PTR [esi+1224]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1344]
	adc edx, DWORD PTR [esi+1348]
	add eax, DWORD PTR [esi+1224]
	adc edx, DWORD PTR [esi+1228]
	mov DWORD PTR [esi+1224], eax
	mov DWORD PTR [esi+1228], edx
	mov eax, DWORD PTR [esi+1984]
	mov edx, DWORD PTR [esi+1988]
	xor eax, DWORD PTR [esi+1224]
	xor edx, DWORD PTR [esi+1228]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1984], edx
	mov DWORD PTR [esi+1988], eax
	mov edx, DWORD PTR [esi+1984]
	mov eax, DWORD PTR [esi+1608]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1984]
	adc edx, DWORD PTR [esi+1988]
	add eax, DWORD PTR [esi+1608]
	adc edx, DWORD PTR [esi+1612]
	mov DWORD PTR [esi+1608], eax
	mov DWORD PTR [esi+1612], edx
	mov eax, DWORD PTR [esi+1344]
	mov edx, DWORD PTR [esi+1348]
	xor eax, DWORD PTR [esi+1608]
	xor edx, DWORD PTR [esi+1612]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1344], eax
	mov DWORD PTR [esi+1348], edx
	mov edx, DWORD PTR [esi+1360]
	mov eax, DWORD PTR [esi+1104]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1360]
	adc edx, DWORD PTR [esi+1364]
	add eax, DWORD PTR [esi+1104]
	adc edx, DWORD PTR [esi+1108]
	mov DWORD PTR [esi+1104], eax
	mov DWORD PTR [esi+1108], edx
	mov eax, DWORD PTR [esi+1872]
	mov edx, DWORD PTR [esi+1876]
	xor eax, DWORD PTR [esi+1104]
	xor edx, DWORD PTR [esi+1108]
	mov DWORD PTR [esi+1872], edx
	mov DWORD PTR [esi+1876], eax
	mov edx, DWORD PTR [esi+1872]
	mov eax, DWORD PTR [esi+1616]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1872]
	adc edx, DWORD PTR [esi+1876]
	add eax, DWORD PTR [esi+1616]
	adc edx, DWORD PTR [esi+1620]
	mov DWORD PTR [esi+1616], eax
	mov DWORD PTR [esi+1620], edx
	mov eax, DWORD PTR [esi+1360]
	mov edx, DWORD PTR [esi+1364]
	xor eax, DWORD PTR [esi+1616]
	xor edx, DWORD PTR [esi+1620]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1360], edx
	mov DWORD PTR [esi+1364], eax
	mov edx, DWORD PTR [esi+1360]
	mov eax, DWORD PTR [esi+1104]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1360]
	adc edx, DWORD PTR [esi+1364]
	add eax, DWORD PTR [esi+1104]
	adc edx, DWORD PTR [esi+1108]
	mov DWORD PTR [esi+1104], eax
	mov DWORD PTR [esi+1108], edx
	mov eax, DWORD PTR [esi+1872]
	mov edx, DWORD PTR [esi+1876]
	xor eax, DWORD PTR [esi+1104]
	xor edx, DWORD PTR [esi+1108]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1872], edx
	mov DWORD PTR [esi+1876], eax
	mov edx, DWORD PTR [esi+1872]
	mov eax, DWORD PTR [esi+1616]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1872]
	adc edx, DWORD PTR [esi+1876]
	add eax, DWORD PTR [esi+1616]
	adc edx, DWORD PTR [esi+1620]
	mov DWORD PTR [esi+1616], eax
	mov DWORD PTR [esi+1620], edx
	mov eax, DWORD PTR [esi+1360]
	mov edx, DWORD PTR [esi+1364]
	xor eax, DWORD PTR [esi+1616]
	xor edx, DWORD PTR [esi+1620]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1360], eax
	mov DWORD PTR [esi+1364], edx
	mov edx, DWORD PTR [esi+1368]
	mov eax, DWORD PTR [esi+1112]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1368]
	adc edx, DWORD PTR [esi+1372]
	add eax, DWORD PTR [esi+1112]
	adc edx, DWORD PTR [esi+1116]
	mov DWORD PTR [esi+1112], eax
	mov DWORD PTR [esi+1116], edx
	mov eax, DWORD PTR [esi+1880]
	mov edx, DWORD PTR [esi+1884]
	xor eax, DWORD PTR [esi+1112]
	xor edx, DWORD PTR [esi+1116]
	mov DWORD PTR [esi+1880], edx
	mov DWORD PTR [esi+1884], eax
	mov edx, DWORD PTR [esi+1880]
	mov eax, DWORD PTR [esi+1624]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1880]
	adc edx, DWORD PTR [esi+1884]
	add eax, DWORD PTR [esi+1624]
	adc edx, DWORD PTR [esi+1628]
	mov DWORD PTR [esi+1624], eax
	mov DWORD PTR [esi+1628], edx
	mov eax, DWORD PTR [esi+1368]
	mov edx, DWORD PTR [esi+1372]
	xor eax, DWORD PTR [esi+1624]
	xor edx, DWORD PTR [esi+1628]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1368], edx
	mov DWORD PTR [esi+1372], eax
	mov edx, DWORD PTR [esi+1368]
	mov eax, DWORD PTR [esi+1112]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1368]
	adc edx, DWORD PTR [esi+1372]
	add eax, DWORD PTR [esi+1112]
	adc edx, DWORD PTR [esi+1116]
	mov DWORD PTR [esi+1112], eax
	mov DWORD PTR [esi+1116], edx
	mov eax, DWORD PTR [esi+1880]
	mov edx, DWORD PTR [esi+1884]
	xor eax, DWORD PTR [esi+1112]
	xor edx, DWORD PTR [esi+1116]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1880], edx
	mov DWORD PTR [esi+1884], eax
	mov edx, DWORD PTR [esi+1880]
	mov eax, DWORD PTR [esi+1624]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1880]
	adc edx, DWORD PTR [esi+1884]
	add eax, DWORD PTR [esi+1624]
	adc edx, DWORD PTR [esi+1628]
	mov DWORD PTR [esi+1624], eax
	mov DWORD PTR [esi+1628], edx
	mov eax, DWORD PTR [esi+1368]
	mov edx, DWORD PTR [esi+1372]
	xor eax, DWORD PTR [esi+1624]
	xor edx, DWORD PTR [esi+1628]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1368], eax
	mov DWORD PTR [esi+1372], edx
	mov edx, DWORD PTR [esi+1488]
	mov eax, DWORD PTR [esi+1232]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1488]
	adc edx, DWORD PTR [esi+1492]
	add eax, DWORD PTR [esi+1232]
	adc edx, DWORD PTR [esi+1236]
	mov DWORD PTR [esi+1232], eax
	mov DWORD PTR [esi+1236], edx
	mov eax, DWORD PTR [esi+2000]
	mov edx, DWORD PTR [esi+2004]
	xor eax, DWORD PTR [esi+1232]
	xor edx, DWORD PTR [esi+1236]
	mov DWORD PTR [esi+2000], edx
	mov DWORD PTR [esi+2004], eax
	mov edx, DWORD PTR [esi+2000]
	mov eax, DWORD PTR [esi+1744]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2000]
	adc edx, DWORD PTR [esi+2004]
	add eax, DWORD PTR [esi+1744]
	adc edx, DWORD PTR [esi+1748]
	mov DWORD PTR [esi+1744], eax
	mov DWORD PTR [esi+1748], edx
	mov eax, DWORD PTR [esi+1488]
	mov edx, DWORD PTR [esi+1492]
	xor eax, DWORD PTR [esi+1744]
	xor edx, DWORD PTR [esi+1748]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1488], edx
	mov DWORD PTR [esi+1492], eax
	mov edx, DWORD PTR [esi+1488]
	mov eax, DWORD PTR [esi+1232]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1488]
	adc edx, DWORD PTR [esi+1492]
	add eax, DWORD PTR [esi+1232]
	adc edx, DWORD PTR [esi+1236]
	mov DWORD PTR [esi+1232], eax
	mov DWORD PTR [esi+1236], edx
	mov eax, DWORD PTR [esi+2000]
	mov edx, DWORD PTR [esi+2004]
	xor eax, DWORD PTR [esi+1232]
	xor edx, DWORD PTR [esi+1236]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2000], edx
	mov DWORD PTR [esi+2004], eax
	mov edx, DWORD PTR [esi+2000]
	mov eax, DWORD PTR [esi+1744]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2000]
	adc edx, DWORD PTR [esi+2004]
	add eax, DWORD PTR [esi+1744]
	adc edx, DWORD PTR [esi+1748]
	mov DWORD PTR [esi+1744], eax
	mov DWORD PTR [esi+1748], edx
	mov eax, DWORD PTR [esi+1488]
	mov edx, DWORD PTR [esi+1492]
	xor eax, DWORD PTR [esi+1744]
	xor edx, DWORD PTR [esi+1748]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1488], eax
	mov DWORD PTR [esi+1492], edx
	mov edx, DWORD PTR [esi+1496]
	mov eax, DWORD PTR [esi+1240]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1496]
	adc edx, DWORD PTR [esi+1500]
	add eax, DWORD PTR [esi+1240]
	adc edx, DWORD PTR [esi+1244]
	mov DWORD PTR [esi+1240], eax
	mov DWORD PTR [esi+1244], edx
	mov eax, DWORD PTR [esi+2008]
	mov edx, DWORD PTR [esi+2012]
	xor eax, DWORD PTR [esi+1240]
	xor edx, DWORD PTR [esi+1244]
	mov DWORD PTR [esi+2008], edx
	mov DWORD PTR [esi+2012], eax
	mov edx, DWORD PTR [esi+2008]
	mov eax, DWORD PTR [esi+1752]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2008]
	adc edx, DWORD PTR [esi+2012]
	add eax, DWORD PTR [esi+1752]
	adc edx, DWORD PTR [esi+1756]
	mov DWORD PTR [esi+1752], eax
	mov DWORD PTR [esi+1756], edx
	mov eax, DWORD PTR [esi+1496]
	mov edx, DWORD PTR [esi+1500]
	xor eax, DWORD PTR [esi+1752]
	xor edx, DWORD PTR [esi+1756]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1496], edx
	mov DWORD PTR [esi+1500], eax
	mov edx, DWORD PTR [esi+1496]
	mov eax, DWORD PTR [esi+1240]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1496]
	adc edx, DWORD PTR [esi+1500]
	add eax, DWORD PTR [esi+1240]
	adc edx, DWORD PTR [esi+1244]
	mov DWORD PTR [esi+1240], eax
	mov DWORD PTR [esi+1244], edx
	mov eax, DWORD PTR [esi+2008]
	mov edx, DWORD PTR [esi+2012]
	xor eax, DWORD PTR [esi+1240]
	xor edx, DWORD PTR [esi+1244]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2008], edx
	mov DWORD PTR [esi+2012], eax
	mov edx, DWORD PTR [esi+2008]
	mov eax, DWORD PTR [esi+1752]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2008]
	adc edx, DWORD PTR [esi+2012]
	add eax, DWORD PTR [esi+1752]
	adc edx, DWORD PTR [esi+1756]
	mov DWORD PTR [esi+1752], eax
	mov DWORD PTR [esi+1756], edx
	mov eax, DWORD PTR [esi+1496]
	mov edx, DWORD PTR [esi+1500]
	xor eax, DWORD PTR [esi+1752]
	xor edx, DWORD PTR [esi+1756]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1496], eax
	mov DWORD PTR [esi+1500], edx
	mov edx, DWORD PTR [esi+1368]
	mov eax, DWORD PTR [esi+1104]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1368]
	adc edx, DWORD PTR [esi+1372]
	add eax, DWORD PTR [esi+1104]
	adc edx, DWORD PTR [esi+1108]
	mov DWORD PTR [esi+1104], eax
	mov DWORD PTR [esi+1108], edx
	mov eax, DWORD PTR [esi+2008]
	mov edx, DWORD PTR [esi+2012]
	xor eax, DWORD PTR [esi+1104]
	xor edx, DWORD PTR [esi+1108]
	mov DWORD PTR [esi+2008], edx
	mov DWORD PTR [esi+2012], eax
	mov edx, DWORD PTR [esi+2008]
	mov eax, DWORD PTR [esi+1744]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2008]
	adc edx, DWORD PTR [esi+2012]
	add eax, DWORD PTR [esi+1744]
	adc edx, DWORD PTR [esi+1748]
	mov DWORD PTR [esi+1744], eax
	mov DWORD PTR [esi+1748], edx
	mov eax, DWORD PTR [esi+1368]
	mov edx, DWORD PTR [esi+1372]
	xor eax, DWORD PTR [esi+1744]
	xor edx, DWORD PTR [esi+1748]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1368], edx
	mov DWORD PTR [esi+1372], eax
	mov edx, DWORD PTR [esi+1368]
	mov eax, DWORD PTR [esi+1104]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1368]
	adc edx, DWORD PTR [esi+1372]
	add eax, DWORD PTR [esi+1104]
	adc edx, DWORD PTR [esi+1108]
	mov DWORD PTR [esi+1104], eax
	mov DWORD PTR [esi+1108], edx
	mov eax, DWORD PTR [esi+2008]
	mov edx, DWORD PTR [esi+2012]
	xor eax, DWORD PTR [esi+1104]
	xor edx, DWORD PTR [esi+1108]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2008], edx
	mov DWORD PTR [esi+2012], eax
	mov edx, DWORD PTR [esi+2008]
	mov eax, DWORD PTR [esi+1744]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2008]
	adc edx, DWORD PTR [esi+2012]
	add eax, DWORD PTR [esi+1744]
	adc edx, DWORD PTR [esi+1748]
	mov DWORD PTR [esi+1744], eax
	mov DWORD PTR [esi+1748], edx
	mov eax, DWORD PTR [esi+1368]
	mov edx, DWORD PTR [esi+1372]
	xor eax, DWORD PTR [esi+1744]
	xor edx, DWORD PTR [esi+1748]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1368], eax
	mov DWORD PTR [esi+1372], edx
	mov edx, DWORD PTR [esi+1488]
	mov eax, DWORD PTR [esi+1112]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1488]
	adc edx, DWORD PTR [esi+1492]
	add eax, DWORD PTR [esi+1112]
	adc edx, DWORD PTR [esi+1116]
	mov DWORD PTR [esi+1112], eax
	mov DWORD PTR [esi+1116], edx
	mov eax, DWORD PTR [esi+1872]
	mov edx, DWORD PTR [esi+1876]
	xor eax, DWORD PTR [esi+1112]
	xor edx, DWORD PTR [esi+1116]
	mov DWORD PTR [esi+1872], edx
	mov DWORD PTR [esi+1876], eax
	mov edx, DWORD PTR [esi+1872]
	mov eax, DWORD PTR [esi+1752]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1872]
	adc edx, DWORD PTR [esi+1876]
	add eax, DWORD PTR [esi+1752]
	adc edx, DWORD PTR [esi+1756]
	mov DWORD PTR [esi+1752], eax
	mov DWORD PTR [esi+1756], edx
	mov eax, DWORD PTR [esi+1488]
	mov edx, DWORD PTR [esi+1492]
	xor eax, DWORD PTR [esi+1752]
	xor edx, DWORD PTR [esi+1756]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1488], edx
	mov DWORD PTR [esi+1492], eax
	mov edx, DWORD PTR [esi+1488]
	mov eax, DWORD PTR [esi+1112]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1488]
	adc edx, DWORD PTR [esi+1492]
	add eax, DWORD PTR [esi+1112]
	adc edx, DWORD PTR [esi+1116]
	mov DWORD PTR [esi+1112], eax
	mov DWORD PTR [esi+1116], edx
	mov eax, DWORD PTR [esi+1872]
	mov edx, DWORD PTR [esi+1876]
	xor eax, DWORD PTR [esi+1112]
	xor edx, DWORD PTR [esi+1116]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1872], edx
	mov DWORD PTR [esi+1876], eax
	mov edx, DWORD PTR [esi+1872]
	mov eax, DWORD PTR [esi+1752]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1872]
	adc edx, DWORD PTR [esi+1876]
	add eax, DWORD PTR [esi+1752]
	adc edx, DWORD PTR [esi+1756]
	mov DWORD PTR [esi+1752], eax
	mov DWORD PTR [esi+1756], edx
	mov eax, DWORD PTR [esi+1488]
	mov edx, DWORD PTR [esi+1492]
	xor eax, DWORD PTR [esi+1752]
	xor edx, DWORD PTR [esi+1756]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1488], eax
	mov DWORD PTR [esi+1492], edx
	mov edx, DWORD PTR [esi+1496]
	mov eax, DWORD PTR [esi+1232]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1496]
	adc edx, DWORD PTR [esi+1500]
	add eax, DWORD PTR [esi+1232]
	adc edx, DWORD PTR [esi+1236]
	mov DWORD PTR [esi+1232], eax
	mov DWORD PTR [esi+1236], edx
	mov eax, DWORD PTR [esi+1880]
	mov edx, DWORD PTR [esi+1884]
	xor eax, DWORD PTR [esi+1232]
	xor edx, DWORD PTR [esi+1236]
	mov DWORD PTR [esi+1880], edx
	mov DWORD PTR [esi+1884], eax
	mov edx, DWORD PTR [esi+1880]
	mov eax, DWORD PTR [esi+1616]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1880]
	adc edx, DWORD PTR [esi+1884]
	add eax, DWORD PTR [esi+1616]
	adc edx, DWORD PTR [esi+1620]
	mov DWORD PTR [esi+1616], eax
	mov DWORD PTR [esi+1620], edx
	mov eax, DWORD PTR [esi+1496]
	mov edx, DWORD PTR [esi+1500]
	xor eax, DWORD PTR [esi+1616]
	xor edx, DWORD PTR [esi+1620]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1496], edx
	mov DWORD PTR [esi+1500], eax
	mov edx, DWORD PTR [esi+1496]
	mov eax, DWORD PTR [esi+1232]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1496]
	adc edx, DWORD PTR [esi+1500]
	add eax, DWORD PTR [esi+1232]
	adc edx, DWORD PTR [esi+1236]
	mov DWORD PTR [esi+1232], eax
	mov DWORD PTR [esi+1236], edx
	mov eax, DWORD PTR [esi+1880]
	mov edx, DWORD PTR [esi+1884]
	xor eax, DWORD PTR [esi+1232]
	xor edx, DWORD PTR [esi+1236]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1880], edx
	mov DWORD PTR [esi+1884], eax
	mov edx, DWORD PTR [esi+1880]
	mov eax, DWORD PTR [esi+1616]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1880]
	adc edx, DWORD PTR [esi+1884]
	add eax, DWORD PTR [esi+1616]
	adc edx, DWORD PTR [esi+1620]
	mov DWORD PTR [esi+1616], eax
	mov DWORD PTR [esi+1620], edx
	mov eax, DWORD PTR [esi+1496]
	mov edx, DWORD PTR [esi+1500]
	xor eax, DWORD PTR [esi+1616]
	xor edx, DWORD PTR [esi+1620]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1496], eax
	mov DWORD PTR [esi+1500], edx
	mov edx, DWORD PTR [esi+1360]
	mov eax, DWORD PTR [esi+1240]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1360]
	adc edx, DWORD PTR [esi+1364]
	add eax, DWORD PTR [esi+1240]
	adc edx, DWORD PTR [esi+1244]
	mov DWORD PTR [esi+1240], eax
	mov DWORD PTR [esi+1244], edx
	mov eax, DWORD PTR [esi+2000]
	mov edx, DWORD PTR [esi+2004]
	xor eax, DWORD PTR [esi+1240]
	xor edx, DWORD PTR [esi+1244]
	mov DWORD PTR [esi+2000], edx
	mov DWORD PTR [esi+2004], eax
	mov edx, DWORD PTR [esi+2000]
	mov eax, DWORD PTR [esi+1624]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2000]
	adc edx, DWORD PTR [esi+2004]
	add eax, DWORD PTR [esi+1624]
	adc edx, DWORD PTR [esi+1628]
	mov DWORD PTR [esi+1624], eax
	mov DWORD PTR [esi+1628], edx
	mov eax, DWORD PTR [esi+1360]
	mov edx, DWORD PTR [esi+1364]
	xor eax, DWORD PTR [esi+1624]
	xor edx, DWORD PTR [esi+1628]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1360], edx
	mov DWORD PTR [esi+1364], eax
	mov edx, DWORD PTR [esi+1360]
	mov eax, DWORD PTR [esi+1240]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1360]
	adc edx, DWORD PTR [esi+1364]
	add eax, DWORD PTR [esi+1240]
	adc edx, DWORD PTR [esi+1244]
	mov DWORD PTR [esi+1240], eax
	mov DWORD PTR [esi+1244], edx
	mov eax, DWORD PTR [esi+2000]
	mov edx, DWORD PTR [esi+2004]
	xor eax, DWORD PTR [esi+1240]
	xor edx, DWORD PTR [esi+1244]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2000], edx
	mov DWORD PTR [esi+2004], eax
	mov edx, DWORD PTR [esi+2000]
	mov eax, DWORD PTR [esi+1624]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2000]
	adc edx, DWORD PTR [esi+2004]
	add eax, DWORD PTR [esi+1624]
	adc edx, DWORD PTR [esi+1628]
	mov DWORD PTR [esi+1624], eax
	mov DWORD PTR [esi+1628], edx
	mov eax, DWORD PTR [esi+1360]
	mov edx, DWORD PTR [esi+1364]
	xor eax, DWORD PTR [esi+1624]
	xor edx, DWORD PTR [esi+1628]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1360], eax
	mov DWORD PTR [esi+1364], edx
	mov edx, DWORD PTR [esi+1376]
	mov eax, DWORD PTR [esi+1120]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1376]
	adc edx, DWORD PTR [esi+1380]
	add eax, DWORD PTR [esi+1120]
	adc edx, DWORD PTR [esi+1124]
	mov DWORD PTR [esi+1120], eax
	mov DWORD PTR [esi+1124], edx
	mov eax, DWORD PTR [esi+1888]
	mov edx, DWORD PTR [esi+1892]
	xor eax, DWORD PTR [esi+1120]
	xor edx, DWORD PTR [esi+1124]
	mov DWORD PTR [esi+1888], edx
	mov DWORD PTR [esi+1892], eax
	mov edx, DWORD PTR [esi+1888]
	mov eax, DWORD PTR [esi+1632]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1888]
	adc edx, DWORD PTR [esi+1892]
	add eax, DWORD PTR [esi+1632]
	adc edx, DWORD PTR [esi+1636]
	mov DWORD PTR [esi+1632], eax
	mov DWORD PTR [esi+1636], edx
	mov eax, DWORD PTR [esi+1376]
	mov edx, DWORD PTR [esi+1380]
	xor eax, DWORD PTR [esi+1632]
	xor edx, DWORD PTR [esi+1636]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1376], edx
	mov DWORD PTR [esi+1380], eax
	mov edx, DWORD PTR [esi+1376]
	mov eax, DWORD PTR [esi+1120]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1376]
	adc edx, DWORD PTR [esi+1380]
	add eax, DWORD PTR [esi+1120]
	adc edx, DWORD PTR [esi+1124]
	mov DWORD PTR [esi+1120], eax
	mov DWORD PTR [esi+1124], edx
	mov eax, DWORD PTR [esi+1888]
	mov edx, DWORD PTR [esi+1892]
	xor eax, DWORD PTR [esi+1120]
	xor edx, DWORD PTR [esi+1124]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1888], edx
	mov DWORD PTR [esi+1892], eax
	mov edx, DWORD PTR [esi+1888]
	mov eax, DWORD PTR [esi+1632]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1888]
	adc edx, DWORD PTR [esi+1892]
	add eax, DWORD PTR [esi+1632]
	adc edx, DWORD PTR [esi+1636]
	mov DWORD PTR [esi+1632], eax
	mov DWORD PTR [esi+1636], edx
	mov eax, DWORD PTR [esi+1376]
	mov edx, DWORD PTR [esi+1380]
	xor eax, DWORD PTR [esi+1632]
	xor edx, DWORD PTR [esi+1636]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1376], eax
	mov DWORD PTR [esi+1380], edx
	mov edx, DWORD PTR [esi+1384]
	mov eax, DWORD PTR [esi+1128]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1384]
	adc edx, DWORD PTR [esi+1388]
	add eax, DWORD PTR [esi+1128]
	adc edx, DWORD PTR [esi+1132]
	mov DWORD PTR [esi+1128], eax
	mov DWORD PTR [esi+1132], edx
	mov eax, DWORD PTR [esi+1896]
	mov edx, DWORD PTR [esi+1900]
	xor eax, DWORD PTR [esi+1128]
	xor edx, DWORD PTR [esi+1132]
	mov DWORD PTR [esi+1896], edx
	mov DWORD PTR [esi+1900], eax
	mov edx, DWORD PTR [esi+1896]
	mov eax, DWORD PTR [esi+1640]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1896]
	adc edx, DWORD PTR [esi+1900]
	add eax, DWORD PTR [esi+1640]
	adc edx, DWORD PTR [esi+1644]
	mov DWORD PTR [esi+1640], eax
	mov DWORD PTR [esi+1644], edx
	mov eax, DWORD PTR [esi+1384]
	mov edx, DWORD PTR [esi+1388]
	xor eax, DWORD PTR [esi+1640]
	xor edx, DWORD PTR [esi+1644]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1384], edx
	mov DWORD PTR [esi+1388], eax
	mov edx, DWORD PTR [esi+1384]
	mov eax, DWORD PTR [esi+1128]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1384]
	adc edx, DWORD PTR [esi+1388]
	add eax, DWORD PTR [esi+1128]
	adc edx, DWORD PTR [esi+1132]
	mov DWORD PTR [esi+1128], eax
	mov DWORD PTR [esi+1132], edx
	mov eax, DWORD PTR [esi+1896]
	mov edx, DWORD PTR [esi+1900]
	xor eax, DWORD PTR [esi+1128]
	xor edx, DWORD PTR [esi+1132]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1896], edx
	mov DWORD PTR [esi+1900], eax
	mov edx, DWORD PTR [esi+1896]
	mov eax, DWORD PTR [esi+1640]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1896]
	adc edx, DWORD PTR [esi+1900]
	add eax, DWORD PTR [esi+1640]
	adc edx, DWORD PTR [esi+1644]
	mov DWORD PTR [esi+1640], eax
	mov DWORD PTR [esi+1644], edx
	mov eax, DWORD PTR [esi+1384]
	mov edx, DWORD PTR [esi+1388]
	xor eax, DWORD PTR [esi+1640]
	xor edx, DWORD PTR [esi+1644]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1384], eax
	mov DWORD PTR [esi+1388], edx
	mov edx, DWORD PTR [esi+1504]
	mov eax, DWORD PTR [esi+1248]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1504]
	adc edx, DWORD PTR [esi+1508]
	add eax, DWORD PTR [esi+1248]
	adc edx, DWORD PTR [esi+1252]
	mov DWORD PTR [esi+1248], eax
	mov DWORD PTR [esi+1252], edx
	mov eax, DWORD PTR [esi+2016]
	mov edx, DWORD PTR [esi+2020]
	xor eax, DWORD PTR [esi+1248]
	xor edx, DWORD PTR [esi+1252]
	mov DWORD PTR [esi+2016], edx
	mov DWORD PTR [esi+2020], eax
	mov edx, DWORD PTR [esi+2016]
	mov eax, DWORD PTR [esi+1760]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2016]
	adc edx, DWORD PTR [esi+2020]
	add eax, DWORD PTR [esi+1760]
	adc edx, DWORD PTR [esi+1764]
	mov DWORD PTR [esi+1760], eax
	mov DWORD PTR [esi+1764], edx
	mov eax, DWORD PTR [esi+1504]
	mov edx, DWORD PTR [esi+1508]
	xor eax, DWORD PTR [esi+1760]
	xor edx, DWORD PTR [esi+1764]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1504], edx
	mov DWORD PTR [esi+1508], eax
	mov edx, DWORD PTR [esi+1504]
	mov eax, DWORD PTR [esi+1248]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1504]
	adc edx, DWORD PTR [esi+1508]
	add eax, DWORD PTR [esi+1248]
	adc edx, DWORD PTR [esi+1252]
	mov DWORD PTR [esi+1248], eax
	mov DWORD PTR [esi+1252], edx
	mov eax, DWORD PTR [esi+2016]
	mov edx, DWORD PTR [esi+2020]
	xor eax, DWORD PTR [esi+1248]
	xor edx, DWORD PTR [esi+1252]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2016], edx
	mov DWORD PTR [esi+2020], eax
	mov edx, DWORD PTR [esi+2016]
	mov eax, DWORD PTR [esi+1760]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2016]
	adc edx, DWORD PTR [esi+2020]
	add eax, DWORD PTR [esi+1760]
	adc edx, DWORD PTR [esi+1764]
	mov DWORD PTR [esi+1760], eax
	mov DWORD PTR [esi+1764], edx
	mov eax, DWORD PTR [esi+1504]
	mov edx, DWORD PTR [esi+1508]
	xor eax, DWORD PTR [esi+1760]
	xor edx, DWORD PTR [esi+1764]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1504], eax
	mov DWORD PTR [esi+1508], edx
	mov edx, DWORD PTR [esi+1512]
	mov eax, DWORD PTR [esi+1256]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1512]
	adc edx, DWORD PTR [esi+1516]
	add eax, DWORD PTR [esi+1256]
	adc edx, DWORD PTR [esi+1260]
	mov DWORD PTR [esi+1256], eax
	mov DWORD PTR [esi+1260], edx
	mov eax, DWORD PTR [esi+2024]
	mov edx, DWORD PTR [esi+2028]
	xor eax, DWORD PTR [esi+1256]
	xor edx, DWORD PTR [esi+1260]
	mov DWORD PTR [esi+2024], edx
	mov DWORD PTR [esi+2028], eax
	mov edx, DWORD PTR [esi+2024]
	mov eax, DWORD PTR [esi+1768]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2024]
	adc edx, DWORD PTR [esi+2028]
	add eax, DWORD PTR [esi+1768]
	adc edx, DWORD PTR [esi+1772]
	mov DWORD PTR [esi+1768], eax
	mov DWORD PTR [esi+1772], edx
	mov eax, DWORD PTR [esi+1512]
	mov edx, DWORD PTR [esi+1516]
	xor eax, DWORD PTR [esi+1768]
	xor edx, DWORD PTR [esi+1772]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1512], edx
	mov DWORD PTR [esi+1516], eax
	mov edx, DWORD PTR [esi+1512]
	mov eax, DWORD PTR [esi+1256]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1512]
	adc edx, DWORD PTR [esi+1516]
	add eax, DWORD PTR [esi+1256]
	adc edx, DWORD PTR [esi+1260]
	mov DWORD PTR [esi+1256], eax
	mov DWORD PTR [esi+1260], edx
	mov eax, DWORD PTR [esi+2024]
	mov edx, DWORD PTR [esi+2028]
	xor eax, DWORD PTR [esi+1256]
	xor edx, DWORD PTR [esi+1260]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2024], edx
	mov DWORD PTR [esi+2028], eax
	mov edx, DWORD PTR [esi+2024]
	mov eax, DWORD PTR [esi+1768]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2024]
	adc edx, DWORD PTR [esi+2028]
	add eax, DWORD PTR [esi+1768]
	adc edx, DWORD PTR [esi+1772]
	mov DWORD PTR [esi+1768], eax
	mov DWORD PTR [esi+1772], edx
	mov eax, DWORD PTR [esi+1512]
	mov edx, DWORD PTR [esi+1516]
	xor eax, DWORD PTR [esi+1768]
	xor edx, DWORD PTR [esi+1772]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1512], eax
	mov DWORD PTR [esi+1516], edx
	mov edx, DWORD PTR [esi+1384]
	mov eax, DWORD PTR [esi+1120]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1384]
	adc edx, DWORD PTR [esi+1388]
	add eax, DWORD PTR [esi+1120]
	adc edx, DWORD PTR [esi+1124]
	mov DWORD PTR [esi+1120], eax
	mov DWORD PTR [esi+1124], edx
	mov eax, DWORD PTR [esi+2024]
	mov edx, DWORD PTR [esi+2028]
	xor eax, DWORD PTR [esi+1120]
	xor edx, DWORD PTR [esi+1124]
	mov DWORD PTR [esi+2024], edx
	mov DWORD PTR [esi+2028], eax
	mov edx, DWORD PTR [esi+2024]
	mov eax, DWORD PTR [esi+1760]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2024]
	adc edx, DWORD PTR [esi+2028]
	add eax, DWORD PTR [esi+1760]
	adc edx, DWORD PTR [esi+1764]
	mov DWORD PTR [esi+1760], eax
	mov DWORD PTR [esi+1764], edx
	mov eax, DWORD PTR [esi+1384]
	mov edx, DWORD PTR [esi+1388]
	xor eax, DWORD PTR [esi+1760]
	xor edx, DWORD PTR [esi+1764]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1384], edx
	mov DWORD PTR [esi+1388], eax
	mov edx, DWORD PTR [esi+1384]
	mov eax, DWORD PTR [esi+1120]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1384]
	adc edx, DWORD PTR [esi+1388]
	add eax, DWORD PTR [esi+1120]
	adc edx, DWORD PTR [esi+1124]
	mov DWORD PTR [esi+1120], eax
	mov DWORD PTR [esi+1124], edx
	mov eax, DWORD PTR [esi+2024]
	mov edx, DWORD PTR [esi+2028]
	xor eax, DWORD PTR [esi+1120]
	xor edx, DWORD PTR [esi+1124]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2024], edx
	mov DWORD PTR [esi+2028], eax
	mov edx, DWORD PTR [esi+2024]
	mov eax, DWORD PTR [esi+1760]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2024]
	adc edx, DWORD PTR [esi+2028]
	add eax, DWORD PTR [esi+1760]
	adc edx, DWORD PTR [esi+1764]
	mov DWORD PTR [esi+1760], eax
	mov DWORD PTR [esi+1764], edx
	mov eax, DWORD PTR [esi+1384]
	mov edx, DWORD PTR [esi+1388]
	xor eax, DWORD PTR [esi+1760]
	xor edx, DWORD PTR [esi+1764]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1384], eax
	mov DWORD PTR [esi+1388], edx
	mov edx, DWORD PTR [esi+1504]
	mov eax, DWORD PTR [esi+1128]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1504]
	adc edx, DWORD PTR [esi+1508]
	add eax, DWORD PTR [esi+1128]
	adc edx, DWORD PTR [esi+1132]
	mov DWORD PTR [esi+1128], eax
	mov DWORD PTR [esi+1132], edx
	mov eax, DWORD PTR [esi+1888]
	mov edx, DWORD PTR [esi+1892]
	xor eax, DWORD PTR [esi+1128]
	xor edx, DWORD PTR [esi+1132]
	mov DWORD PTR [esi+1888], edx
	mov DWORD PTR [esi+1892], eax
	mov edx, DWORD PTR [esi+1888]
	mov eax, DWORD PTR [esi+1768]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1888]
	adc edx, DWORD PTR [esi+1892]
	add eax, DWORD PTR [esi+1768]
	adc edx, DWORD PTR [esi+1772]
	mov DWORD PTR [esi+1768], eax
	mov DWORD PTR [esi+1772], edx
	mov eax, DWORD PTR [esi+1504]
	mov edx, DWORD PTR [esi+1508]
	xor eax, DWORD PTR [esi+1768]
	xor edx, DWORD PTR [esi+1772]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1504], edx
	mov DWORD PTR [esi+1508], eax
	mov edx, DWORD PTR [esi+1504]
	mov eax, DWORD PTR [esi+1128]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1504]
	adc edx, DWORD PTR [esi+1508]
	add eax, DWORD PTR [esi+1128]
	adc edx, DWORD PTR [esi+1132]
	mov DWORD PTR [esi+1128], eax
	mov DWORD PTR [esi+1132], edx
	mov eax, DWORD PTR [esi+1888]
	mov edx, DWORD PTR [esi+1892]
	xor eax, DWORD PTR [esi+1128]
	xor edx, DWORD PTR [esi+1132]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1888], edx
	mov DWORD PTR [esi+1892], eax
	mov edx, DWORD PTR [esi+1888]
	mov eax, DWORD PTR [esi+1768]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1888]
	adc edx, DWORD PTR [esi+1892]
	add eax, DWORD PTR [esi+1768]
	adc edx, DWORD PTR [esi+1772]
	mov DWORD PTR [esi+1768], eax
	mov DWORD PTR [esi+1772], edx
	mov eax, DWORD PTR [esi+1504]
	mov edx, DWORD PTR [esi+1508]
	xor eax, DWORD PTR [esi+1768]
	xor edx, DWORD PTR [esi+1772]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1504], eax
	mov DWORD PTR [esi+1508], edx
	mov edx, DWORD PTR [esi+1512]
	mov eax, DWORD PTR [esi+1248]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1512]
	adc edx, DWORD PTR [esi+1516]
	add eax, DWORD PTR [esi+1248]
	adc edx, DWORD PTR [esi+1252]
	mov DWORD PTR [esi+1248], eax
	mov DWORD PTR [esi+1252], edx
	mov eax, DWORD PTR [esi+1896]
	mov edx, DWORD PTR [esi+1900]
	xor eax, DWORD PTR [esi+1248]
	xor edx, DWORD PTR [esi+1252]
	mov DWORD PTR [esi+1896], edx
	mov DWORD PTR [esi+1900], eax
	mov edx, DWORD PTR [esi+1896]
	mov eax, DWORD PTR [esi+1632]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1896]
	adc edx, DWORD PTR [esi+1900]
	add eax, DWORD PTR [esi+1632]
	adc edx, DWORD PTR [esi+1636]
	mov DWORD PTR [esi+1632], eax
	mov DWORD PTR [esi+1636], edx
	mov eax, DWORD PTR [esi+1512]
	mov edx, DWORD PTR [esi+1516]
	xor eax, DWORD PTR [esi+1632]
	xor edx, DWORD PTR [esi+1636]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1512], edx
	mov DWORD PTR [esi+1516], eax
	mov edx, DWORD PTR [esi+1512]
	mov eax, DWORD PTR [esi+1248]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1512]
	adc edx, DWORD PTR [esi+1516]
	add eax, DWORD PTR [esi+1248]
	adc edx, DWORD PTR [esi+1252]
	mov DWORD PTR [esi+1248], eax
	mov DWORD PTR [esi+1252], edx
	mov eax, DWORD PTR [esi+1896]
	mov edx, DWORD PTR [esi+1900]
	xor eax, DWORD PTR [esi+1248]
	xor edx, DWORD PTR [esi+1252]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1896], edx
	mov DWORD PTR [esi+1900], eax
	mov edx, DWORD PTR [esi+1896]
	mov eax, DWORD PTR [esi+1632]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1896]
	adc edx, DWORD PTR [esi+1900]
	add eax, DWORD PTR [esi+1632]
	adc edx, DWORD PTR [esi+1636]
	mov DWORD PTR [esi+1632], eax
	mov DWORD PTR [esi+1636], edx
	mov eax, DWORD PTR [esi+1512]
	mov edx, DWORD PTR [esi+1516]
	xor eax, DWORD PTR [esi+1632]
	xor edx, DWORD PTR [esi+1636]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1512], eax
	mov DWORD PTR [esi+1516], edx
	mov edx, DWORD PTR [esi+1376]
	mov eax, DWORD PTR [esi+1256]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1376]
	adc edx, DWORD PTR [esi+1380]
	add eax, DWORD PTR [esi+1256]
	adc edx, DWORD PTR [esi+1260]
	mov DWORD PTR [esi+1256], eax
	mov DWORD PTR [esi+1260], edx
	mov eax, DWORD PTR [esi+2016]
	mov edx, DWORD PTR [esi+2020]
	xor eax, DWORD PTR [esi+1256]
	xor edx, DWORD PTR [esi+1260]
	mov DWORD PTR [esi+2016], edx
	mov DWORD PTR [esi+2020], eax
	mov edx, DWORD PTR [esi+2016]
	mov eax, DWORD PTR [esi+1640]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2016]
	adc edx, DWORD PTR [esi+2020]
	add eax, DWORD PTR [esi+1640]
	adc edx, DWORD PTR [esi+1644]
	mov DWORD PTR [esi+1640], eax
	mov DWORD PTR [esi+1644], edx
	mov eax, DWORD PTR [esi+1376]
	mov edx, DWORD PTR [esi+1380]
	xor eax, DWORD PTR [esi+1640]
	xor edx, DWORD PTR [esi+1644]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1376], edx
	mov DWORD PTR [esi+1380], eax
	mov edx, DWORD PTR [esi+1376]
	mov eax, DWORD PTR [esi+1256]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1376]
	adc edx, DWORD PTR [esi+1380]
	add eax, DWORD PTR [esi+1256]
	adc edx, DWORD PTR [esi+1260]
	mov DWORD PTR [esi+1256], eax
	mov DWORD PTR [esi+1260], edx
	mov eax, DWORD PTR [esi+2016]
	mov edx, DWORD PTR [esi+2020]
	xor eax, DWORD PTR [esi+1256]
	xor edx, DWORD PTR [esi+1260]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2016], edx
	mov DWORD PTR [esi+2020], eax
	mov edx, DWORD PTR [esi+2016]
	mov eax, DWORD PTR [esi+1640]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2016]
	adc edx, DWORD PTR [esi+2020]
	add eax, DWORD PTR [esi+1640]
	adc edx, DWORD PTR [esi+1644]
	mov DWORD PTR [esi+1640], eax
	mov DWORD PTR [esi+1644], edx
	mov eax, DWORD PTR [esi+1376]
	mov edx, DWORD PTR [esi+1380]
	xor eax, DWORD PTR [esi+1640]
	xor edx, DWORD PTR [esi+1644]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1376], eax
	mov DWORD PTR [esi+1380], edx
	mov edx, DWORD PTR [esi+1392]
	mov eax, DWORD PTR [esi+1136]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1392]
	adc edx, DWORD PTR [esi+1396]
	add eax, DWORD PTR [esi+1136]
	adc edx, DWORD PTR [esi+1140]
	mov DWORD PTR [esi+1136], eax
	mov DWORD PTR [esi+1140], edx
	mov eax, DWORD PTR [esi+1904]
	mov edx, DWORD PTR [esi+1908]
	xor eax, DWORD PTR [esi+1136]
	xor edx, DWORD PTR [esi+1140]
	mov DWORD PTR [esi+1904], edx
	mov DWORD PTR [esi+1908], eax
	mov edx, DWORD PTR [esi+1904]
	mov eax, DWORD PTR [esi+1648]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1904]
	adc edx, DWORD PTR [esi+1908]
	add eax, DWORD PTR [esi+1648]
	adc edx, DWORD PTR [esi+1652]
	mov DWORD PTR [esi+1648], eax
	mov DWORD PTR [esi+1652], edx
	mov eax, DWORD PTR [esi+1392]
	mov edx, DWORD PTR [esi+1396]
	xor eax, DWORD PTR [esi+1648]
	xor edx, DWORD PTR [esi+1652]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1392], edx
	mov DWORD PTR [esi+1396], eax
	mov edx, DWORD PTR [esi+1392]
	mov eax, DWORD PTR [esi+1136]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1392]
	adc edx, DWORD PTR [esi+1396]
	add eax, DWORD PTR [esi+1136]
	adc edx, DWORD PTR [esi+1140]
	mov DWORD PTR [esi+1136], eax
	mov DWORD PTR [esi+1140], edx
	mov eax, DWORD PTR [esi+1904]
	mov edx, DWORD PTR [esi+1908]
	xor eax, DWORD PTR [esi+1136]
	xor edx, DWORD PTR [esi+1140]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1904], edx
	mov DWORD PTR [esi+1908], eax
	mov edx, DWORD PTR [esi+1904]
	mov eax, DWORD PTR [esi+1648]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1904]
	adc edx, DWORD PTR [esi+1908]
	add eax, DWORD PTR [esi+1648]
	adc edx, DWORD PTR [esi+1652]
	mov DWORD PTR [esi+1648], eax
	mov DWORD PTR [esi+1652], edx
	mov eax, DWORD PTR [esi+1392]
	mov edx, DWORD PTR [esi+1396]
	xor eax, DWORD PTR [esi+1648]
	xor edx, DWORD PTR [esi+1652]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1392], eax
	mov DWORD PTR [esi+1396], edx
	mov edx, DWORD PTR [esi+1400]
	mov eax, DWORD PTR [esi+1144]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1400]
	adc edx, DWORD PTR [esi+1404]
	add eax, DWORD PTR [esi+1144]
	adc edx, DWORD PTR [esi+1148]
	mov DWORD PTR [esi+1144], eax
	mov DWORD PTR [esi+1148], edx
	mov eax, DWORD PTR [esi+1912]
	mov edx, DWORD PTR [esi+1916]
	xor eax, DWORD PTR [esi+1144]
	xor edx, DWORD PTR [esi+1148]
	mov DWORD PTR [esi+1912], edx
	mov DWORD PTR [esi+1916], eax
	mov edx, DWORD PTR [esi+1912]
	mov eax, DWORD PTR [esi+1656]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1912]
	adc edx, DWORD PTR [esi+1916]
	add eax, DWORD PTR [esi+1656]
	adc edx, DWORD PTR [esi+1660]
	mov DWORD PTR [esi+1656], eax
	mov DWORD PTR [esi+1660], edx
	mov eax, DWORD PTR [esi+1400]
	mov edx, DWORD PTR [esi+1404]
	xor eax, DWORD PTR [esi+1656]
	xor edx, DWORD PTR [esi+1660]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1400], edx
	mov DWORD PTR [esi+1404], eax
	mov edx, DWORD PTR [esi+1400]
	mov eax, DWORD PTR [esi+1144]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1400]
	adc edx, DWORD PTR [esi+1404]
	add eax, DWORD PTR [esi+1144]
	adc edx, DWORD PTR [esi+1148]
	mov DWORD PTR [esi+1144], eax
	mov DWORD PTR [esi+1148], edx
	mov eax, DWORD PTR [esi+1912]
	mov edx, DWORD PTR [esi+1916]
	xor eax, DWORD PTR [esi+1144]
	xor edx, DWORD PTR [esi+1148]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1912], edx
	mov DWORD PTR [esi+1916], eax
	mov edx, DWORD PTR [esi+1912]
	mov eax, DWORD PTR [esi+1656]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1912]
	adc edx, DWORD PTR [esi+1916]
	add eax, DWORD PTR [esi+1656]
	adc edx, DWORD PTR [esi+1660]
	mov DWORD PTR [esi+1656], eax
	mov DWORD PTR [esi+1660], edx
	mov eax, DWORD PTR [esi+1400]
	mov edx, DWORD PTR [esi+1404]
	xor eax, DWORD PTR [esi+1656]
	xor edx, DWORD PTR [esi+1660]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1400], eax
	mov DWORD PTR [esi+1404], edx
	mov edx, DWORD PTR [esi+1520]
	mov eax, DWORD PTR [esi+1264]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1520]
	adc edx, DWORD PTR [esi+1524]
	add eax, DWORD PTR [esi+1264]
	adc edx, DWORD PTR [esi+1268]
	mov DWORD PTR [esi+1264], eax
	mov DWORD PTR [esi+1268], edx
	mov eax, DWORD PTR [esi+2032]
	mov edx, DWORD PTR [esi+2036]
	xor eax, DWORD PTR [esi+1264]
	xor edx, DWORD PTR [esi+1268]
	mov DWORD PTR [esi+2032], edx
	mov DWORD PTR [esi+2036], eax
	mov edx, DWORD PTR [esi+2032]
	mov eax, DWORD PTR [esi+1776]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2032]
	adc edx, DWORD PTR [esi+2036]
	add eax, DWORD PTR [esi+1776]
	adc edx, DWORD PTR [esi+1780]
	mov DWORD PTR [esi+1776], eax
	mov DWORD PTR [esi+1780], edx
	mov eax, DWORD PTR [esi+1520]
	mov edx, DWORD PTR [esi+1524]
	xor eax, DWORD PTR [esi+1776]
	xor edx, DWORD PTR [esi+1780]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1520], edx
	mov DWORD PTR [esi+1524], eax
	mov edx, DWORD PTR [esi+1520]
	mov eax, DWORD PTR [esi+1264]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1520]
	adc edx, DWORD PTR [esi+1524]
	add eax, DWORD PTR [esi+1264]
	adc edx, DWORD PTR [esi+1268]
	mov DWORD PTR [esi+1264], eax
	mov DWORD PTR [esi+1268], edx
	mov eax, DWORD PTR [esi+2032]
	mov edx, DWORD PTR [esi+2036]
	xor eax, DWORD PTR [esi+1264]
	xor edx, DWORD PTR [esi+1268]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2032], edx
	mov DWORD PTR [esi+2036], eax
	mov edx, DWORD PTR [esi+2032]
	mov eax, DWORD PTR [esi+1776]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2032]
	adc edx, DWORD PTR [esi+2036]
	add eax, DWORD PTR [esi+1776]
	adc edx, DWORD PTR [esi+1780]
	mov DWORD PTR [esi+1776], eax
	mov DWORD PTR [esi+1780], edx
	mov eax, DWORD PTR [esi+1520]
	mov edx, DWORD PTR [esi+1524]
	xor eax, DWORD PTR [esi+1776]
	xor edx, DWORD PTR [esi+1780]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1520], eax
	mov DWORD PTR [esi+1524], edx
	mov edx, DWORD PTR [esi+1528]
	mov eax, DWORD PTR [esi+1272]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1528]
	adc edx, DWORD PTR [esi+1532]
	add eax, DWORD PTR [esi+1272]
	adc edx, DWORD PTR [esi+1276]
	mov DWORD PTR [esi+1272], eax
	mov DWORD PTR [esi+1276], edx
	mov eax, DWORD PTR [esi+2040]
	mov edx, DWORD PTR [esi+2044]
	xor eax, DWORD PTR [esi+1272]
	xor edx, DWORD PTR [esi+1276]
	mov DWORD PTR [esi+2040], edx
	mov DWORD PTR [esi+2044], eax
	mov edx, DWORD PTR [esi+2040]
	mov eax, DWORD PTR [esi+1784]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2040]
	adc edx, DWORD PTR [esi+2044]
	add eax, DWORD PTR [esi+1784]
	adc edx, DWORD PTR [esi+1788]
	mov DWORD PTR [esi+1784], eax
	mov DWORD PTR [esi+1788], edx
	mov eax, DWORD PTR [esi+1528]
	mov edx, DWORD PTR [esi+1532]
	xor eax, DWORD PTR [esi+1784]
	xor edx, DWORD PTR [esi+1788]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1528], edx
	mov DWORD PTR [esi+1532], eax
	mov edx, DWORD PTR [esi+1528]
	mov eax, DWORD PTR [esi+1272]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1528]
	adc edx, DWORD PTR [esi+1532]
	add eax, DWORD PTR [esi+1272]
	adc edx, DWORD PTR [esi+1276]
	mov DWORD PTR [esi+1272], eax
	mov DWORD PTR [esi+1276], edx
	mov eax, DWORD PTR [esi+2040]
	mov edx, DWORD PTR [esi+2044]
	xor eax, DWORD PTR [esi+1272]
	xor edx, DWORD PTR [esi+1276]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2040], edx
	mov DWORD PTR [esi+2044], eax
	mov edx, DWORD PTR [esi+2040]
	mov eax, DWORD PTR [esi+1784]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2040]
	adc edx, DWORD PTR [esi+2044]
	add eax, DWORD PTR [esi+1784]
	adc edx, DWORD PTR [esi+1788]
	mov DWORD PTR [esi+1784], eax
	mov DWORD PTR [esi+1788], edx
	mov eax, DWORD PTR [esi+1528]
	mov edx, DWORD PTR [esi+1532]
	xor eax, DWORD PTR [esi+1784]
	xor edx, DWORD PTR [esi+1788]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1528], eax
	mov DWORD PTR [esi+1532], edx
	mov edx, DWORD PTR [esi+1400]
	mov eax, DWORD PTR [esi+1136]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1400]
	adc edx, DWORD PTR [esi+1404]
	add eax, DWORD PTR [esi+1136]
	adc edx, DWORD PTR [esi+1140]
	mov DWORD PTR [esi+1136], eax
	mov DWORD PTR [esi+1140], edx
	mov eax, DWORD PTR [esi+2040]
	mov edx, DWORD PTR [esi+2044]
	xor eax, DWORD PTR [esi+1136]
	xor edx, DWORD PTR [esi+1140]
	mov DWORD PTR [esi+2040], edx
	mov DWORD PTR [esi+2044], eax
	mov edx, DWORD PTR [esi+2040]
	mov eax, DWORD PTR [esi+1776]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2040]
	adc edx, DWORD PTR [esi+2044]
	add eax, DWORD PTR [esi+1776]
	adc edx, DWORD PTR [esi+1780]
	mov DWORD PTR [esi+1776], eax
	mov DWORD PTR [esi+1780], edx
	mov eax, DWORD PTR [esi+1400]
	mov edx, DWORD PTR [esi+1404]
	xor eax, DWORD PTR [esi+1776]
	xor edx, DWORD PTR [esi+1780]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1400], edx
	mov DWORD PTR [esi+1404], eax
	mov edx, DWORD PTR [esi+1400]
	mov eax, DWORD PTR [esi+1136]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1400]
	adc edx, DWORD PTR [esi+1404]
	add eax, DWORD PTR [esi+1136]
	adc edx, DWORD PTR [esi+1140]
	mov DWORD PTR [esi+1136], eax
	mov DWORD PTR [esi+1140], edx
	mov eax, DWORD PTR [esi+2040]
	mov edx, DWORD PTR [esi+2044]
	xor eax, DWORD PTR [esi+1136]
	xor edx, DWORD PTR [esi+1140]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2040], edx
	mov DWORD PTR [esi+2044], eax
	mov edx, DWORD PTR [esi+2040]
	mov eax, DWORD PTR [esi+1776]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2040]
	adc edx, DWORD PTR [esi+2044]
	add eax, DWORD PTR [esi+1776]
	adc edx, DWORD PTR [esi+1780]
	mov DWORD PTR [esi+1776], eax
	mov DWORD PTR [esi+1780], edx
	mov eax, DWORD PTR [esi+1400]
	mov edx, DWORD PTR [esi+1404]
	xor eax, DWORD PTR [esi+1776]
	xor edx, DWORD PTR [esi+1780]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1400], eax
	mov DWORD PTR [esi+1404], edx
	mov edx, DWORD PTR [esi+1520]
	mov eax, DWORD PTR [esi+1144]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1520]
	adc edx, DWORD PTR [esi+1524]
	add eax, DWORD PTR [esi+1144]
	adc edx, DWORD PTR [esi+1148]
	mov DWORD PTR [esi+1144], eax
	mov DWORD PTR [esi+1148], edx
	mov eax, DWORD PTR [esi+1904]
	mov edx, DWORD PTR [esi+1908]
	xor eax, DWORD PTR [esi+1144]
	xor edx, DWORD PTR [esi+1148]
	mov DWORD PTR [esi+1904], edx
	mov DWORD PTR [esi+1908], eax
	mov edx, DWORD PTR [esi+1904]
	mov eax, DWORD PTR [esi+1784]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1904]
	adc edx, DWORD PTR [esi+1908]
	add eax, DWORD PTR [esi+1784]
	adc edx, DWORD PTR [esi+1788]
	mov DWORD PTR [esi+1784], eax
	mov DWORD PTR [esi+1788], edx
	mov eax, DWORD PTR [esi+1520]
	mov edx, DWORD PTR [esi+1524]
	xor eax, DWORD PTR [esi+1784]
	xor edx, DWORD PTR [esi+1788]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1520], edx
	mov DWORD PTR [esi+1524], eax
	mov edx, DWORD PTR [esi+1520]
	mov eax, DWORD PTR [esi+1144]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1520]
	adc edx, DWORD PTR [esi+1524]
	add eax, DWORD PTR [esi+1144]
	adc edx, DWORD PTR [esi+1148]
	mov DWORD PTR [esi+1144], eax
	mov DWORD PTR [esi+1148], edx
	mov eax, DWORD PTR [esi+1904]
	mov edx, DWORD PTR [esi+1908]
	xor eax, DWORD PTR [esi+1144]
	xor edx, DWORD PTR [esi+1148]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1904], edx
	mov DWORD PTR [esi+1908], eax
	mov edx, DWORD PTR [esi+1904]
	mov eax, DWORD PTR [esi+1784]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1904]
	adc edx, DWORD PTR [esi+1908]
	add eax, DWORD PTR [esi+1784]
	adc edx, DWORD PTR [esi+1788]
	mov DWORD PTR [esi+1784], eax
	mov DWORD PTR [esi+1788], edx
	mov eax, DWORD PTR [esi+1520]
	mov edx, DWORD PTR [esi+1524]
	xor eax, DWORD PTR [esi+1784]
	xor edx, DWORD PTR [esi+1788]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1520], eax
	mov DWORD PTR [esi+1524], edx
	mov edx, DWORD PTR [esi+1528]
	mov eax, DWORD PTR [esi+1264]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1528]
	adc edx, DWORD PTR [esi+1532]
	add eax, DWORD PTR [esi+1264]
	adc edx, DWORD PTR [esi+1268]
	mov DWORD PTR [esi+1264], eax
	mov DWORD PTR [esi+1268], edx
	mov eax, DWORD PTR [esi+1912]
	mov edx, DWORD PTR [esi+1916]
	xor eax, DWORD PTR [esi+1264]
	xor edx, DWORD PTR [esi+1268]
	mov DWORD PTR [esi+1912], edx
	mov DWORD PTR [esi+1916], eax
	mov edx, DWORD PTR [esi+1912]
	mov eax, DWORD PTR [esi+1648]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1912]
	adc edx, DWORD PTR [esi+1916]
	add eax, DWORD PTR [esi+1648]
	adc edx, DWORD PTR [esi+1652]
	mov DWORD PTR [esi+1648], eax
	mov DWORD PTR [esi+1652], edx
	mov eax, DWORD PTR [esi+1528]
	mov edx, DWORD PTR [esi+1532]
	xor eax, DWORD PTR [esi+1648]
	xor edx, DWORD PTR [esi+1652]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1528], edx
	mov DWORD PTR [esi+1532], eax
	mov edx, DWORD PTR [esi+1528]
	mov eax, DWORD PTR [esi+1264]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1528]
	adc edx, DWORD PTR [esi+1532]
	add eax, DWORD PTR [esi+1264]
	adc edx, DWORD PTR [esi+1268]
	mov DWORD PTR [esi+1264], eax
	mov DWORD PTR [esi+1268], edx
	mov eax, DWORD PTR [esi+1912]
	mov edx, DWORD PTR [esi+1916]
	xor eax, DWORD PTR [esi+1264]
	xor edx, DWORD PTR [esi+1268]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1912], edx
	mov DWORD PTR [esi+1916], eax
	mov edx, DWORD PTR [esi+1912]
	mov eax, DWORD PTR [esi+1648]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1912]
	adc edx, DWORD PTR [esi+1916]
	add eax, DWORD PTR [esi+1648]
	adc edx, DWORD PTR [esi+1652]
	mov DWORD PTR [esi+1648], eax
	mov DWORD PTR [esi+1652], edx
	mov eax, DWORD PTR [esi+1528]
	mov edx, DWORD PTR [esi+1532]
	xor eax, DWORD PTR [esi+1648]
	xor edx, DWORD PTR [esi+1652]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1528], eax
	mov DWORD PTR [esi+1532], edx
	mov edx, DWORD PTR [esi+1392]
	mov eax, DWORD PTR [esi+1272]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1392]
	adc edx, DWORD PTR [esi+1396]
	add eax, DWORD PTR [esi+1272]
	adc edx, DWORD PTR [esi+1276]
	mov DWORD PTR [esi+1272], eax
	mov DWORD PTR [esi+1276], edx
	mov eax, DWORD PTR [esi+2032]
	mov edx, DWORD PTR [esi+2036]
	xor eax, DWORD PTR [esi+1272]
	xor edx, DWORD PTR [esi+1276]
	mov DWORD PTR [esi+2032], edx
	mov DWORD PTR [esi+2036], eax
	mov edx, DWORD PTR [esi+2032]
	mov eax, DWORD PTR [esi+1656]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2032]
	adc edx, DWORD PTR [esi+2036]
	add eax, DWORD PTR [esi+1656]
	adc edx, DWORD PTR [esi+1660]
	mov DWORD PTR [esi+1656], eax
	mov DWORD PTR [esi+1660], edx
	mov eax, DWORD PTR [esi+1392]
	mov edx, DWORD PTR [esi+1396]
	xor eax, DWORD PTR [esi+1656]
	xor edx, DWORD PTR [esi+1660]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, 255
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+1392], edx
	mov DWORD PTR [esi+1396], eax
	mov edx, DWORD PTR [esi+1392]
	mov eax, DWORD PTR [esi+1272]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+1392]
	adc edx, DWORD PTR [esi+1396]
	add eax, DWORD PTR [esi+1272]
	adc edx, DWORD PTR [esi+1276]
	mov DWORD PTR [esi+1272], eax
	mov DWORD PTR [esi+1276], edx
	mov eax, DWORD PTR [esi+2032]
	mov edx, DWORD PTR [esi+2036]
	xor eax, DWORD PTR [esi+1272]
	xor edx, DWORD PTR [esi+1276]
	ror eax, 16
	ror edx, 16
	mov ecx, eax
	xor ecx, edx
	and ecx, 65535
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [esi+2032], edx
	mov DWORD PTR [esi+2036], eax
	mov edx, DWORD PTR [esi+2032]
	mov eax, DWORD PTR [esi+1656]
	mul edx
	add eax, eax
	adc edx, edx
	add eax, DWORD PTR [esi+2032]
	adc edx, DWORD PTR [esi+2036]
	add eax, DWORD PTR [esi+1656]
	adc edx, DWORD PTR [esi+1660]
	mov DWORD PTR [esi+1656], eax
	mov DWORD PTR [esi+1660], edx
	mov eax, DWORD PTR [esi+1392]
	mov edx, DWORD PTR [esi+1396]
	xor eax, DWORD PTR [esi+1656]
	xor edx, DWORD PTR [esi+1660]
	ror edx, 31
	ror eax, 31
	mov ecx, edx
	xor ecx, eax
	and ecx, 1
	xor edx, ecx
	xor eax, ecx
	mov DWORD PTR [esi+1392], eax
	mov DWORD PTR [esi+1396], edx
	mov ecx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi+1024]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [ecx], eax
	mov eax, DWORD PTR [esi+1028]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [ecx+4], eax
	mov eax, DWORD PTR [esi+1032]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [ecx+8], eax
	mov eax, DWORD PTR [esi+1036]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [ecx+12], eax
	mov eax, DWORD PTR [esi+1040]
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [ecx+16], eax
	mov eax, DWORD PTR [esi+1044]
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [ecx+20], eax
	mov eax, DWORD PTR [esi+1048]
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [ecx+24], eax
	mov eax, DWORD PTR [esi+1052]
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [ecx+28], eax
	mov eax, DWORD PTR [esi+1056]
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [ecx+32], eax
	mov eax, DWORD PTR [esi+1060]
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [ecx+36], eax
	mov eax, DWORD PTR [esi+1064]
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [ecx+40], eax
	mov eax, DWORD PTR [esi+1068]
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [ecx+44], eax
	mov eax, DWORD PTR [esi+1072]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [ecx+48], eax
	mov eax, DWORD PTR [esi+1076]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [ecx+52], eax
	mov eax, DWORD PTR [esi+1080]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [ecx+56], eax
	mov eax, DWORD PTR [esi+1084]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [ecx+60], eax
	mov eax, DWORD PTR [esi+1088]
	xor eax, DWORD PTR [esi+64]
	mov DWORD PTR [ecx+64], eax
	mov eax, DWORD PTR [esi+1092]
	xor eax, DWORD PTR [esi+68]
	mov DWORD PTR [ecx+68], eax
	mov eax, DWORD PTR [esi+1096]
	xor eax, DWORD PTR [esi+72]
	mov DWORD PTR [ecx+72], eax
	mov eax, DWORD PTR [esi+1100]
	xor eax, DWORD PTR [esi+76]
	mov DWORD PTR [ecx+76], eax
	mov eax, DWORD PTR [esi+1104]
	xor eax, DWORD PTR [esi+80]
	mov DWORD PTR [ecx+80], eax
	mov eax, DWORD PTR [esi+1108]
	xor eax, DWORD PTR [esi+84]
	mov DWORD PTR [ecx+84], eax
	mov eax, DWORD PTR [esi+1112]
	xor eax, DWORD PTR [esi+88]
	mov DWORD PTR [ecx+88], eax
	mov eax, DWORD PTR [esi+1116]
	xor eax, DWORD PTR [esi+92]
	mov DWORD PTR [ecx+92], eax
	mov eax, DWORD PTR [esi+1120]
	xor eax, DWORD PTR [esi+96]
	mov DWORD PTR [ecx+96], eax
	mov eax, DWORD PTR [esi+1124]
	xor eax, DWORD PTR [esi+100]
	mov DWORD PTR [ecx+100], eax
	mov eax, DWORD PTR [esi+1128]
	xor eax, DWORD PTR [esi+104]
	mov DWORD PTR [ecx+104], eax
	mov eax, DWORD PTR [esi+1132]
	xor eax, DWORD PTR [esi+108]
	mov DWORD PTR [ecx+108], eax
	mov eax, DWORD PTR [esi+1136]
	xor eax, DWORD PTR [esi+112]
	mov DWORD PTR [ecx+112], eax
	mov eax, DWORD PTR [esi+1140]
	xor eax, DWORD PTR [esi+116]
	mov DWORD PTR [ecx+116], eax
	mov eax, DWORD PTR [esi+1144]
	xor eax, DWORD PTR [esi+120]
	mov DWORD PTR [ecx+120], eax
	mov eax, DWORD PTR [esi+1148]
	xor eax, DWORD PTR [esi+124]
	mov DWORD PTR [ecx+124], eax
	mov eax, DWORD PTR [esi+1152]
	xor eax, DWORD PTR [esi+128]
	mov DWORD PTR [ecx+128], eax
	mov eax, DWORD PTR [esi+1156]
	xor eax, DWORD PTR [esi+132]
	mov DWORD PTR [ecx+132], eax
	mov eax, DWORD PTR [esi+1160]
	xor eax, DWORD PTR [esi+136]
	mov DWORD PTR [ecx+136], eax
	mov eax, DWORD PTR [esi+1164]
	xor eax, DWORD PTR [esi+140]
	mov DWORD PTR [ecx+140], eax
	mov eax, DWORD PTR [esi+1168]
	xor eax, DWORD PTR [esi+144]
	mov DWORD PTR [ecx+144], eax
	mov eax, DWORD PTR [esi+1172]
	xor eax, DWORD PTR [esi+148]
	mov DWORD PTR [ecx+148], eax
	mov eax, DWORD PTR [esi+1176]
	xor eax, DWORD PTR [esi+152]
	mov DWORD PTR [ecx+152], eax
	mov eax, DWORD PTR [esi+1180]
	xor eax, DWORD PTR [esi+156]
	mov DWORD PTR [ecx+156], eax
	mov eax, DWORD PTR [esi+1184]
	xor eax, DWORD PTR [esi+160]
	mov DWORD PTR [ecx+160], eax
	mov eax, DWORD PTR [esi+1188]
	xor eax, DWORD PTR [esi+164]
	mov DWORD PTR [ecx+164], eax
	mov eax, DWORD PTR [esi+1192]
	xor eax, DWORD PTR [esi+168]
	mov DWORD PTR [ecx+168], eax
	mov eax, DWORD PTR [esi+1196]
	xor eax, DWORD PTR [esi+172]
	mov DWORD PTR [ecx+172], eax
	mov eax, DWORD PTR [esi+1200]
	xor eax, DWORD PTR [esi+176]
	mov DWORD PTR [ecx+176], eax
	mov eax, DWORD PTR [esi+1204]
	xor eax, DWORD PTR [esi+180]
	mov DWORD PTR [ecx+180], eax
	mov eax, DWORD PTR [esi+1208]
	xor eax, DWORD PTR [esi+184]
	mov DWORD PTR [ecx+184], eax
	mov eax, DWORD PTR [esi+1212]
	xor eax, DWORD PTR [esi+188]
	mov DWORD PTR [ecx+188], eax
	mov eax, DWORD PTR [esi+1216]
	xor eax, DWORD PTR [esi+192]
	mov DWORD PTR [ecx+192], eax
	mov eax, DWORD PTR [esi+1220]
	xor eax, DWORD PTR [esi+196]
	mov DWORD PTR [ecx+196], eax
	mov eax, DWORD PTR [esi+1224]
	xor eax, DWORD PTR [esi+200]
	mov DWORD PTR [ecx+200], eax
	mov eax, DWORD PTR [esi+1228]
	xor eax, DWORD PTR [esi+204]
	mov DWORD PTR [ecx+204], eax
	mov eax, DWORD PTR [esi+1232]
	xor eax, DWORD PTR [esi+208]
	mov DWORD PTR [ecx+208], eax
	mov eax, DWORD PTR [esi+1236]
	xor eax, DWORD PTR [esi+212]
	mov DWORD PTR [ecx+212], eax
	mov eax, DWORD PTR [esi+1240]
	xor eax, DWORD PTR [esi+216]
	mov DWORD PTR [ecx+216], eax
	mov eax, DWORD PTR [esi+1244]
	xor eax, DWORD PTR [esi+220]
	mov DWORD PTR [ecx+220], eax
	mov eax, DWORD PTR [esi+1248]
	xor eax, DWORD PTR [esi+224]
	mov DWORD PTR [ecx+224], eax
	mov eax, DWORD PTR [esi+1252]
	xor eax, DWORD PTR [esi+228]
	mov DWORD PTR [ecx+228], eax
	mov eax, DWORD PTR [esi+1256]
	xor eax, DWORD PTR [esi+232]
	mov DWORD PTR [ecx+232], eax
	mov eax, DWORD PTR [esi+1260]
	xor eax, DWORD PTR [esi+236]
	mov DWORD PTR [ecx+236], eax
	mov eax, DWORD PTR [esi+1264]
	xor eax, DWORD PTR [esi+240]
	mov DWORD PTR [ecx+240], eax
	mov eax, DWORD PTR [esi+1268]
	xor eax, DWORD PTR [esi+244]
	mov DWORD PTR [ecx+244], eax
	mov eax, DWORD PTR [esi+1272]
	xor eax, DWORD PTR [esi+248]
	mov DWORD PTR [ecx+248], eax
	mov eax, DWORD PTR [esi+1276]
	xor eax, DWORD PTR [esi+252]
	mov DWORD PTR [ecx+252], eax
	mov eax, DWORD PTR [esi+1280]
	xor eax, DWORD PTR [esi+256]
	mov DWORD PTR [ecx+256], eax
	mov eax, DWORD PTR [esi+1284]
	xor eax, DWORD PTR [esi+260]
	mov DWORD PTR [ecx+260], eax
	mov eax, DWORD PTR [esi+1288]
	xor eax, DWORD PTR [esi+264]
	mov DWORD PTR [ecx+264], eax
	mov eax, DWORD PTR [esi+1292]
	xor eax, DWORD PTR [esi+268]
	mov DWORD PTR [ecx+268], eax
	mov eax, DWORD PTR [esi+1296]
	xor eax, DWORD PTR [esi+272]
	mov DWORD PTR [ecx+272], eax
	mov eax, DWORD PTR [esi+1300]
	xor eax, DWORD PTR [esi+276]
	mov DWORD PTR [ecx+276], eax
	mov eax, DWORD PTR [esi+1304]
	xor eax, DWORD PTR [esi+280]
	mov DWORD PTR [ecx+280], eax
	mov eax, DWORD PTR [esi+1308]
	xor eax, DWORD PTR [esi+284]
	mov DWORD PTR [ecx+284], eax
	mov eax, DWORD PTR [esi+1312]
	xor eax, DWORD PTR [esi+288]
	mov DWORD PTR [ecx+288], eax
	mov eax, DWORD PTR [esi+1316]
	xor eax, DWORD PTR [esi+292]
	mov DWORD PTR [ecx+292], eax
	mov eax, DWORD PTR [esi+1320]
	xor eax, DWORD PTR [esi+296]
	mov DWORD PTR [ecx+296], eax
	mov eax, DWORD PTR [esi+1324]
	xor eax, DWORD PTR [esi+300]
	mov DWORD PTR [ecx+300], eax
	mov eax, DWORD PTR [esi+1328]
	xor eax, DWORD PTR [esi+304]
	mov DWORD PTR [ecx+304], eax
	mov eax, DWORD PTR [esi+1332]
	xor eax, DWORD PTR [esi+308]
	mov DWORD PTR [ecx+308], eax
	mov eax, DWORD PTR [esi+1336]
	xor eax, DWORD PTR [esi+312]
	mov DWORD PTR [ecx+312], eax
	mov eax, DWORD PTR [esi+1340]
	xor eax, DWORD PTR [esi+316]
	mov DWORD PTR [ecx+316], eax
	mov eax, DWORD PTR [esi+1344]
	xor eax, DWORD PTR [esi+320]
	mov DWORD PTR [ecx+320], eax
	mov eax, DWORD PTR [esi+1348]
	xor eax, DWORD PTR [esi+324]
	mov DWORD PTR [ecx+324], eax
	mov eax, DWORD PTR [esi+1352]
	xor eax, DWORD PTR [esi+328]
	mov DWORD PTR [ecx+328], eax
	mov eax, DWORD PTR [esi+1356]
	xor eax, DWORD PTR [esi+332]
	mov DWORD PTR [ecx+332], eax
	mov eax, DWORD PTR [esi+1360]
	xor eax, DWORD PTR [esi+336]
	mov DWORD PTR [ecx+336], eax
	mov eax, DWORD PTR [esi+1364]
	xor eax, DWORD PTR [esi+340]
	mov DWORD PTR [ecx+340], eax
	mov eax, DWORD PTR [esi+1368]
	xor eax, DWORD PTR [esi+344]
	mov DWORD PTR [ecx+344], eax
	mov eax, DWORD PTR [esi+1372]
	xor eax, DWORD PTR [esi+348]
	mov DWORD PTR [ecx+348], eax
	mov eax, DWORD PTR [esi+1376]
	xor eax, DWORD PTR [esi+352]
	mov DWORD PTR [ecx+352], eax
	mov eax, DWORD PTR [esi+1380]
	xor eax, DWORD PTR [esi+356]
	mov DWORD PTR [ecx+356], eax
	mov eax, DWORD PTR [esi+1384]
	xor eax, DWORD PTR [esi+360]
	mov DWORD PTR [ecx+360], eax
	mov eax, DWORD PTR [esi+1388]
	xor eax, DWORD PTR [esi+364]
	mov DWORD PTR [ecx+364], eax
	mov eax, DWORD PTR [esi+1392]
	xor eax, DWORD PTR [esi+368]
	mov DWORD PTR [ecx+368], eax
	mov eax, DWORD PTR [esi+1396]
	xor eax, DWORD PTR [esi+372]
	mov DWORD PTR [ecx+372], eax
	mov eax, DWORD PTR [esi+1400]
	xor eax, DWORD PTR [esi+376]
	mov DWORD PTR [ecx+376], eax
	mov eax, DWORD PTR [esi+1404]
	xor eax, DWORD PTR [esi+380]
	mov DWORD PTR [ecx+380], eax
	mov eax, DWORD PTR [esi+1408]
	xor eax, DWORD PTR [esi+384]
	mov DWORD PTR [ecx+384], eax
	mov eax, DWORD PTR [esi+1412]
	xor eax, DWORD PTR [esi+388]
	mov DWORD PTR [ecx+388], eax
	mov eax, DWORD PTR [esi+1416]
	xor eax, DWORD PTR [esi+392]
	mov DWORD PTR [ecx+392], eax
	mov eax, DWORD PTR [esi+1420]
	xor eax, DWORD PTR [esi+396]
	mov DWORD PTR [ecx+396], eax
	mov eax, DWORD PTR [esi+1424]
	xor eax, DWORD PTR [esi+400]
	mov DWORD PTR [ecx+400], eax
	mov eax, DWORD PTR [esi+1428]
	xor eax, DWORD PTR [esi+404]
	mov DWORD PTR [ecx+404], eax
	mov eax, DWORD PTR [esi+1432]
	xor eax, DWORD PTR [esi+408]
	mov DWORD PTR [ecx+408], eax
	mov eax, DWORD PTR [esi+1436]
	xor eax, DWORD PTR [esi+412]
	mov DWORD PTR [ecx+412], eax
	mov eax, DWORD PTR [esi+1440]
	xor eax, DWORD PTR [esi+416]
	mov DWORD PTR [ecx+416], eax
	mov eax, DWORD PTR [esi+1444]
	xor eax, DWORD PTR [esi+420]
	mov DWORD PTR [ecx+420], eax
	mov eax, DWORD PTR [esi+1448]
	xor eax, DWORD PTR [esi+424]
	mov DWORD PTR [ecx+424], eax
	mov eax, DWORD PTR [esi+1452]
	xor eax, DWORD PTR [esi+428]
	mov DWORD PTR [ecx+428], eax
	mov eax, DWORD PTR [esi+1456]
	xor eax, DWORD PTR [esi+432]
	mov DWORD PTR [ecx+432], eax
	mov eax, DWORD PTR [esi+1460]
	xor eax, DWORD PTR [esi+436]
	mov DWORD PTR [ecx+436], eax
	mov eax, DWORD PTR [esi+1464]
	xor eax, DWORD PTR [esi+440]
	mov DWORD PTR [ecx+440], eax
	mov eax, DWORD PTR [esi+1468]
	xor eax, DWORD PTR [esi+444]
	mov DWORD PTR [ecx+444], eax
	mov eax, DWORD PTR [esi+1472]
	xor eax, DWORD PTR [esi+448]
	mov DWORD PTR [ecx+448], eax
	mov eax, DWORD PTR [esi+1476]
	xor eax, DWORD PTR [esi+452]
	mov DWORD PTR [ecx+452], eax
	mov eax, DWORD PTR [esi+1480]
	xor eax, DWORD PTR [esi+456]
	mov DWORD PTR [ecx+456], eax
	mov eax, DWORD PTR [esi+1484]
	xor eax, DWORD PTR [esi+460]
	mov DWORD PTR [ecx+460], eax
	mov eax, DWORD PTR [esi+1488]
	xor eax, DWORD PTR [esi+464]
	mov DWORD PTR [ecx+464], eax
	mov eax, DWORD PTR [esi+1492]
	xor eax, DWORD PTR [esi+468]
	mov DWORD PTR [ecx+468], eax
	mov eax, DWORD PTR [esi+1496]
	xor eax, DWORD PTR [esi+472]
	mov DWORD PTR [ecx+472], eax
	mov eax, DWORD PTR [esi+1500]
	xor eax, DWORD PTR [esi+476]
	mov DWORD PTR [ecx+476], eax
	mov eax, DWORD PTR [esi+1504]
	xor eax, DWORD PTR [esi+480]
	mov DWORD PTR [ecx+480], eax
	mov eax, DWORD PTR [esi+1508]
	xor eax, DWORD PTR [esi+484]
	mov DWORD PTR [ecx+484], eax
	mov eax, DWORD PTR [esi+1512]
	xor eax, DWORD PTR [esi+488]
	mov DWORD PTR [ecx+488], eax
	mov eax, DWORD PTR [esi+1516]
	xor eax, DWORD PTR [esi+492]
	mov DWORD PTR [ecx+492], eax
	mov eax, DWORD PTR [esi+1520]
	xor eax, DWORD PTR [esi+496]
	mov DWORD PTR [ecx+496], eax
	mov eax, DWORD PTR [esi+1524]
	xor eax, DWORD PTR [esi+500]
	mov DWORD PTR [ecx+500], eax
	mov eax, DWORD PTR [esi+1528]
	xor eax, DWORD PTR [esi+504]
	mov DWORD PTR [ecx+504], eax
	mov eax, DWORD PTR [esi+1532]
	xor eax, DWORD PTR [esi+508]
	mov DWORD PTR [ecx+508], eax
	mov eax, DWORD PTR [esi+1536]
	xor eax, DWORD PTR [esi+512]
	mov DWORD PTR [ecx+512], eax
	mov eax, DWORD PTR [esi+1540]
	xor eax, DWORD PTR [esi+516]
	mov DWORD PTR [ecx+516], eax
	mov eax, DWORD PTR [esi+1544]
	xor eax, DWORD PTR [esi+520]
	mov DWORD PTR [ecx+520], eax
	mov eax, DWORD PTR [esi+1548]
	xor eax, DWORD PTR [esi+524]
	mov DWORD PTR [ecx+524], eax
	mov eax, DWORD PTR [esi+1552]
	xor eax, DWORD PTR [esi+528]
	mov DWORD PTR [ecx+528], eax
	mov eax, DWORD PTR [esi+1556]
	xor eax, DWORD PTR [esi+532]
	mov DWORD PTR [ecx+532], eax
	mov eax, DWORD PTR [esi+1560]
	xor eax, DWORD PTR [esi+536]
	mov DWORD PTR [ecx+536], eax
	mov eax, DWORD PTR [esi+1564]
	xor eax, DWORD PTR [esi+540]
	mov DWORD PTR [ecx+540], eax
	mov eax, DWORD PTR [esi+1568]
	xor eax, DWORD PTR [esi+544]
	mov DWORD PTR [ecx+544], eax
	mov eax, DWORD PTR [esi+1572]
	xor eax, DWORD PTR [esi+548]
	mov DWORD PTR [ecx+548], eax
	mov eax, DWORD PTR [esi+1576]
	xor eax, DWORD PTR [esi+552]
	mov DWORD PTR [ecx+552], eax
	mov eax, DWORD PTR [esi+1580]
	xor eax, DWORD PTR [esi+556]
	mov DWORD PTR [ecx+556], eax
	mov eax, DWORD PTR [esi+1584]
	xor eax, DWORD PTR [esi+560]
	mov DWORD PTR [ecx+560], eax
	mov eax, DWORD PTR [esi+1588]
	xor eax, DWORD PTR [esi+564]
	mov DWORD PTR [ecx+564], eax
	mov eax, DWORD PTR [esi+1592]
	xor eax, DWORD PTR [esi+568]
	mov DWORD PTR [ecx+568], eax
	mov eax, DWORD PTR [esi+1596]
	xor eax, DWORD PTR [esi+572]
	mov DWORD PTR [ecx+572], eax
	mov eax, DWORD PTR [esi+1600]
	xor eax, DWORD PTR [esi+576]
	mov DWORD PTR [ecx+576], eax
	mov eax, DWORD PTR [esi+1604]
	xor eax, DWORD PTR [esi+580]
	mov DWORD PTR [ecx+580], eax
	mov eax, DWORD PTR [esi+1608]
	xor eax, DWORD PTR [esi+584]
	mov DWORD PTR [ecx+584], eax
	mov eax, DWORD PTR [esi+1612]
	xor eax, DWORD PTR [esi+588]
	mov DWORD PTR [ecx+588], eax
	mov eax, DWORD PTR [esi+1616]
	xor eax, DWORD PTR [esi+592]
	mov DWORD PTR [ecx+592], eax
	mov eax, DWORD PTR [esi+1620]
	xor eax, DWORD PTR [esi+596]
	mov DWORD PTR [ecx+596], eax
	mov eax, DWORD PTR [esi+1624]
	xor eax, DWORD PTR [esi+600]
	mov DWORD PTR [ecx+600], eax
	mov eax, DWORD PTR [esi+1628]
	xor eax, DWORD PTR [esi+604]
	mov DWORD PTR [ecx+604], eax
	mov eax, DWORD PTR [esi+1632]
	xor eax, DWORD PTR [esi+608]
	mov DWORD PTR [ecx+608], eax
	mov eax, DWORD PTR [esi+1636]
	xor eax, DWORD PTR [esi+612]
	mov DWORD PTR [ecx+612], eax
	mov eax, DWORD PTR [esi+1640]
	xor eax, DWORD PTR [esi+616]
	mov DWORD PTR [ecx+616], eax
	mov eax, DWORD PTR [esi+1644]
	xor eax, DWORD PTR [esi+620]
	mov DWORD PTR [ecx+620], eax
	mov eax, DWORD PTR [esi+1648]
	xor eax, DWORD PTR [esi+624]
	mov DWORD PTR [ecx+624], eax
	mov eax, DWORD PTR [esi+1652]
	xor eax, DWORD PTR [esi+628]
	mov DWORD PTR [ecx+628], eax
	mov eax, DWORD PTR [esi+1656]
	xor eax, DWORD PTR [esi+632]
	mov DWORD PTR [ecx+632], eax
	mov eax, DWORD PTR [esi+1660]
	xor eax, DWORD PTR [esi+636]
	mov DWORD PTR [ecx+636], eax
	mov eax, DWORD PTR [esi+1664]
	xor eax, DWORD PTR [esi+640]
	mov DWORD PTR [ecx+640], eax
	mov eax, DWORD PTR [esi+1668]
	xor eax, DWORD PTR [esi+644]
	mov DWORD PTR [ecx+644], eax
	mov eax, DWORD PTR [esi+1672]
	xor eax, DWORD PTR [esi+648]
	mov DWORD PTR [ecx+648], eax
	mov eax, DWORD PTR [esi+1676]
	xor eax, DWORD PTR [esi+652]
	mov DWORD PTR [ecx+652], eax
	mov eax, DWORD PTR [esi+1680]
	xor eax, DWORD PTR [esi+656]
	mov DWORD PTR [ecx+656], eax
	mov eax, DWORD PTR [esi+1684]
	xor eax, DWORD PTR [esi+660]
	mov DWORD PTR [ecx+660], eax
	mov eax, DWORD PTR [esi+1688]
	xor eax, DWORD PTR [esi+664]
	mov DWORD PTR [ecx+664], eax
	mov eax, DWORD PTR [esi+1692]
	xor eax, DWORD PTR [esi+668]
	mov DWORD PTR [ecx+668], eax
	mov eax, DWORD PTR [esi+1696]
	xor eax, DWORD PTR [esi+672]
	mov DWORD PTR [ecx+672], eax
	mov eax, DWORD PTR [esi+1700]
	xor eax, DWORD PTR [esi+676]
	mov DWORD PTR [ecx+676], eax
	mov eax, DWORD PTR [esi+1704]
	xor eax, DWORD PTR [esi+680]
	mov DWORD PTR [ecx+680], eax
	mov eax, DWORD PTR [esi+1708]
	xor eax, DWORD PTR [esi+684]
	mov DWORD PTR [ecx+684], eax
	mov eax, DWORD PTR [esi+1712]
	xor eax, DWORD PTR [esi+688]
	mov DWORD PTR [ecx+688], eax
	mov eax, DWORD PTR [esi+1716]
	xor eax, DWORD PTR [esi+692]
	mov DWORD PTR [ecx+692], eax
	mov eax, DWORD PTR [esi+1720]
	xor eax, DWORD PTR [esi+696]
	mov DWORD PTR [ecx+696], eax
	mov eax, DWORD PTR [esi+1724]
	xor eax, DWORD PTR [esi+700]
	mov DWORD PTR [ecx+700], eax
	mov eax, DWORD PTR [esi+1728]
	xor eax, DWORD PTR [esi+704]
	mov DWORD PTR [ecx+704], eax
	mov eax, DWORD PTR [esi+1732]
	xor eax, DWORD PTR [esi+708]
	mov DWORD PTR [ecx+708], eax
	mov eax, DWORD PTR [esi+1736]
	xor eax, DWORD PTR [esi+712]
	mov DWORD PTR [ecx+712], eax
	mov eax, DWORD PTR [esi+1740]
	xor eax, DWORD PTR [esi+716]
	mov DWORD PTR [ecx+716], eax
	mov eax, DWORD PTR [esi+1744]
	xor eax, DWORD PTR [esi+720]
	mov DWORD PTR [ecx+720], eax
	mov eax, DWORD PTR [esi+1748]
	xor eax, DWORD PTR [esi+724]
	mov DWORD PTR [ecx+724], eax
	mov eax, DWORD PTR [esi+1752]
	xor eax, DWORD PTR [esi+728]
	mov DWORD PTR [ecx+728], eax
	mov eax, DWORD PTR [esi+1756]
	xor eax, DWORD PTR [esi+732]
	mov DWORD PTR [ecx+732], eax
	mov eax, DWORD PTR [esi+1760]
	xor eax, DWORD PTR [esi+736]
	mov DWORD PTR [ecx+736], eax
	mov eax, DWORD PTR [esi+1764]
	xor eax, DWORD PTR [esi+740]
	mov DWORD PTR [ecx+740], eax
	mov eax, DWORD PTR [esi+1768]
	xor eax, DWORD PTR [esi+744]
	mov DWORD PTR [ecx+744], eax
	mov eax, DWORD PTR [esi+1772]
	xor eax, DWORD PTR [esi+748]
	mov DWORD PTR [ecx+748], eax
	mov eax, DWORD PTR [esi+1776]
	xor eax, DWORD PTR [esi+752]
	mov DWORD PTR [ecx+752], eax
	mov eax, DWORD PTR [esi+1780]
	xor eax, DWORD PTR [esi+756]
	mov DWORD PTR [ecx+756], eax
	mov eax, DWORD PTR [esi+1784]
	xor eax, DWORD PTR [esi+760]
	mov DWORD PTR [ecx+760], eax
	mov eax, DWORD PTR [esi+1788]
	xor eax, DWORD PTR [esi+764]
	mov DWORD PTR [ecx+764], eax
	mov eax, DWORD PTR [esi+1792]
	xor eax, DWORD PTR [esi+768]
	mov DWORD PTR [ecx+768], eax
	mov eax, DWORD PTR [esi+1796]
	xor eax, DWORD PTR [esi+772]
	mov DWORD PTR [ecx+772], eax
	mov eax, DWORD PTR [esi+1800]
	xor eax, DWORD PTR [esi+776]
	mov DWORD PTR [ecx+776], eax
	mov eax, DWORD PTR [esi+1804]
	xor eax, DWORD PTR [esi+780]
	mov DWORD PTR [ecx+780], eax
	mov eax, DWORD PTR [esi+1808]
	xor eax, DWORD PTR [esi+784]
	mov DWORD PTR [ecx+784], eax
	mov eax, DWORD PTR [esi+1812]
	xor eax, DWORD PTR [esi+788]
	mov DWORD PTR [ecx+788], eax
	mov eax, DWORD PTR [esi+1816]
	xor eax, DWORD PTR [esi+792]
	mov DWORD PTR [ecx+792], eax
	mov eax, DWORD PTR [esi+1820]
	xor eax, DWORD PTR [esi+796]
	mov DWORD PTR [ecx+796], eax
	mov eax, DWORD PTR [esi+1824]
	xor eax, DWORD PTR [esi+800]
	mov DWORD PTR [ecx+800], eax
	mov eax, DWORD PTR [esi+1828]
	xor eax, DWORD PTR [esi+804]
	mov DWORD PTR [ecx+804], eax
	mov eax, DWORD PTR [esi+1832]
	xor eax, DWORD PTR [esi+808]
	mov DWORD PTR [ecx+808], eax
	mov eax, DWORD PTR [esi+1836]
	xor eax, DWORD PTR [esi+812]
	mov DWORD PTR [ecx+812], eax
	mov eax, DWORD PTR [esi+1840]
	xor eax, DWORD PTR [esi+816]
	mov DWORD PTR [ecx+816], eax
	mov eax, DWORD PTR [esi+1844]
	xor eax, DWORD PTR [esi+820]
	mov DWORD PTR [ecx+820], eax
	mov eax, DWORD PTR [esi+1848]
	xor eax, DWORD PTR [esi+824]
	mov DWORD PTR [ecx+824], eax
	mov eax, DWORD PTR [esi+1852]
	xor eax, DWORD PTR [esi+828]
	mov DWORD PTR [ecx+828], eax
	mov eax, DWORD PTR [esi+1856]
	xor eax, DWORD PTR [esi+832]
	mov DWORD PTR [ecx+832], eax
	mov eax, DWORD PTR [esi+1860]
	xor eax, DWORD PTR [esi+836]
	mov DWORD PTR [ecx+836], eax
	mov eax, DWORD PTR [esi+1864]
	xor eax, DWORD PTR [esi+840]
	mov DWORD PTR [ecx+840], eax
	mov eax, DWORD PTR [esi+1868]
	xor eax, DWORD PTR [esi+844]
	mov DWORD PTR [ecx+844], eax
	mov eax, DWORD PTR [esi+1872]
	xor eax, DWORD PTR [esi+848]
	mov DWORD PTR [ecx+848], eax
	mov eax, DWORD PTR [esi+1876]
	xor eax, DWORD PTR [esi+852]
	mov DWORD PTR [ecx+852], eax
	mov eax, DWORD PTR [esi+1880]
	xor eax, DWORD PTR [esi+856]
	mov DWORD PTR [ecx+856], eax
	mov eax, DWORD PTR [esi+1884]
	xor eax, DWORD PTR [esi+860]
	mov DWORD PTR [ecx+860], eax
	mov eax, DWORD PTR [esi+1888]
	xor eax, DWORD PTR [esi+864]
	mov DWORD PTR [ecx+864], eax
	mov eax, DWORD PTR [esi+1892]
	xor eax, DWORD PTR [esi+868]
	mov DWORD PTR [ecx+868], eax
	mov eax, DWORD PTR [esi+1896]
	xor eax, DWORD PTR [esi+872]
	mov DWORD PTR [ecx+872], eax
	mov eax, DWORD PTR [esi+1900]
	xor eax, DWORD PTR [esi+876]
	mov DWORD PTR [ecx+876], eax
	mov eax, DWORD PTR [esi+1904]
	xor eax, DWORD PTR [esi+880]
	mov DWORD PTR [ecx+880], eax
	mov eax, DWORD PTR [esi+1908]
	xor eax, DWORD PTR [esi+884]
	mov DWORD PTR [ecx+884], eax
	mov eax, DWORD PTR [esi+1912]
	xor eax, DWORD PTR [esi+888]
	mov DWORD PTR [ecx+888], eax
	mov eax, DWORD PTR [esi+1916]
	xor eax, DWORD PTR [esi+892]
	mov DWORD PTR [ecx+892], eax
	mov eax, DWORD PTR [esi+1920]
	xor eax, DWORD PTR [esi+896]
	mov DWORD PTR [ecx+896], eax
	mov eax, DWORD PTR [esi+1924]
	xor eax, DWORD PTR [esi+900]
	mov DWORD PTR [ecx+900], eax
	mov eax, DWORD PTR [esi+1928]
	xor eax, DWORD PTR [esi+904]
	mov DWORD PTR [ecx+904], eax
	mov eax, DWORD PTR [esi+1932]
	xor eax, DWORD PTR [esi+908]
	mov DWORD PTR [ecx+908], eax
	mov eax, DWORD PTR [esi+1936]
	xor eax, DWORD PTR [esi+912]
	mov DWORD PTR [ecx+912], eax
	mov eax, DWORD PTR [esi+1940]
	xor eax, DWORD PTR [esi+916]
	mov DWORD PTR [ecx+916], eax
	mov eax, DWORD PTR [esi+1944]
	xor eax, DWORD PTR [esi+920]
	mov DWORD PTR [ecx+920], eax
	mov eax, DWORD PTR [esi+1948]
	xor eax, DWORD PTR [esi+924]
	mov DWORD PTR [ecx+924], eax
	mov eax, DWORD PTR [esi+1952]
	xor eax, DWORD PTR [esi+928]
	mov DWORD PTR [ecx+928], eax
	mov eax, DWORD PTR [esi+1956]
	xor eax, DWORD PTR [esi+932]
	mov DWORD PTR [ecx+932], eax
	mov eax, DWORD PTR [esi+1960]
	xor eax, DWORD PTR [esi+936]
	mov DWORD PTR [ecx+936], eax
	mov eax, DWORD PTR [esi+1964]
	xor eax, DWORD PTR [esi+940]
	mov DWORD PTR [ecx+940], eax
	mov eax, DWORD PTR [esi+1968]
	xor eax, DWORD PTR [esi+944]
	mov DWORD PTR [ecx+944], eax
	mov eax, DWORD PTR [esi+1972]
	xor eax, DWORD PTR [esi+948]
	mov DWORD PTR [ecx+948], eax
	mov eax, DWORD PTR [esi+1976]
	xor eax, DWORD PTR [esi+952]
	mov DWORD PTR [ecx+952], eax
	mov eax, DWORD PTR [esi+1980]
	xor eax, DWORD PTR [esi+956]
	mov DWORD PTR [ecx+956], eax
	mov eax, DWORD PTR [esi+1984]
	xor eax, DWORD PTR [esi+960]
	mov DWORD PTR [ecx+960], eax
	mov eax, DWORD PTR [esi+1988]
	xor eax, DWORD PTR [esi+964]
	mov DWORD PTR [ecx+964], eax
	mov eax, DWORD PTR [esi+1992]
	xor eax, DWORD PTR [esi+968]
	mov DWORD PTR [ecx+968], eax
	mov eax, DWORD PTR [esi+1996]
	xor eax, DWORD PTR [esi+972]
	mov DWORD PTR [ecx+972], eax
	mov eax, DWORD PTR [esi+2000]
	xor eax, DWORD PTR [esi+976]
	mov DWORD PTR [ecx+976], eax
	mov eax, DWORD PTR [esi+2004]
	xor eax, DWORD PTR [esi+980]
	mov DWORD PTR [ecx+980], eax
	mov eax, DWORD PTR [esi+2008]
	xor eax, DWORD PTR [esi+984]
	mov DWORD PTR [ecx+984], eax
	mov eax, DWORD PTR [esi+2012]
	xor eax, DWORD PTR [esi+988]
	mov DWORD PTR [ecx+988], eax
	mov eax, DWORD PTR [esi+2016]
	xor eax, DWORD PTR [esi+992]
	mov DWORD PTR [ecx+992], eax
	mov eax, DWORD PTR [esi+2020]
	xor eax, DWORD PTR [esi+996]
	mov DWORD PTR [ecx+996], eax
	mov eax, DWORD PTR [esi+2024]
	xor eax, DWORD PTR [esi+1000]
	mov DWORD PTR [ecx+1000], eax
	mov eax, DWORD PTR [esi+2028]
	xor eax, DWORD PTR [esi+1004]
	mov DWORD PTR [ecx+1004], eax
	mov eax, DWORD PTR [esi+2032]
	xor eax, DWORD PTR [esi+1008]
	mov DWORD PTR [ecx+1008], eax
	mov eax, DWORD PTR [esi+2036]
	xor eax, DWORD PTR [esi+1012]
	mov DWORD PTR [ecx+1012], eax
	mov eax, DWORD PTR [esi+2040]
	xor eax, DWORD PTR [esi+1016]
	mov DWORD PTR [ecx+1016], eax
	mov eax, DWORD PTR [esi+2044]
	xor eax, DWORD PTR [esi+1020]
	mov DWORD PTR [ecx+1020], eax
	mov esi, DWORD PTR [esi+2048]
	ret
	.p2align 6
