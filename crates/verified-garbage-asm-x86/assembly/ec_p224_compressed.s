// The functions of `src/ec_p224_compressed.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p224_compress_public_key:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1080], eax
	mov eax, 0
	mov DWORD PTR [edi+1084], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1112], eax
	mov eax, 0
	mov DWORD PTR [edi+1116], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1144], eax
	mov eax, 0
	mov DWORD PTR [edi+1148], eax
	mov eax, 1
	mov DWORD PTR [edi+64], eax
	mov eax, 0
	mov DWORD PTR [edi+68], eax
	mov eax, 0
	mov DWORD PTR [edi+72], eax
	mov eax, -1
	mov DWORD PTR [edi+76], eax
	mov eax, -1
	mov DWORD PTR [edi+80], eax
	mov eax, -1
	mov DWORD PTR [edi+84], eax
	mov eax, -1
	mov DWORD PTR [edi+88], eax
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov eax, 1549543997
	mov DWORD PTR [edi+96], eax
	mov eax, 333261125
	mov DWORD PTR [edi+100], eax
	mov eax, -524750786
	mov DWORD PTR [edi+104], eax
	mov eax, -59742
	mov DWORD PTR [edi+108], eax
	mov eax, -1
	mov DWORD PTR [edi+112], eax
	mov eax, -1
	mov DWORD PTR [edi+116], eax
	mov eax, -1
	mov DWORD PTR [edi+120], eax
	mov eax, 0
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
	mov eax, 0
	mov DWORD PTR [edi+224], eax
	mov eax, -1
	mov DWORD PTR [edi+228], eax
	mov eax, -1
	mov DWORD PTR [edi+232], eax
	mov eax, -1
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
	mov eax, 3
	mov DWORD PTR [edi+260], eax
	mov eax, 0
	mov DWORD PTR [edi+264], eax
	mov eax, -1
	mov DWORD PTR [edi+268], eax
	mov eax, -4
	mov DWORD PTR [edi+272], eax
	mov eax, -1
	mov DWORD PTR [edi+276], eax
	mov eax, -1
	mov DWORD PTR [edi+280], eax
	mov eax, 0
	mov DWORD PTR [edi+284], eax
	mov eax, 725683558
	mov DWORD PTR [edi+288], eax
	mov eax, -1237685789
	mov DWORD PTR [edi+292], eax
	mov eax, 1724922162
	mov DWORD PTR [edi+296], eax
	mov eax, 829442268
	mov DWORD PTR [edi+300], eax
	mov eax, 1492616179
	mov DWORD PTR [edi+304], eax
	mov eax, -1184092214
	mov DWORD PTR [edi+308], eax
	mov eax, 2134937273
	mov DWORD PTR [edi+312], eax
	mov eax, 0
	mov DWORD PTR [edi+316], eax
	mov eax, 1829391082
	mov DWORD PTR [edi+320], eax
	mov eax, -1131392474
	mov DWORD PTR [edi+324], eax
	mov eax, 1612234666
	mov DWORD PTR [edi+328], eax
	mov eax, -2061134026
	mov DWORD PTR [edi+332], eax
	mov eax, -110367739
	mov DWORD PTR [edi+336], eax
	mov eax, 1842589595
	mov DWORD PTR [edi+340], eax
	mov eax, -1575264672
	mov DWORD PTR [edi+344], eax
	mov eax, 0
	mov DWORD PTR [edi+348], eax
	mov eax, -269226520
	mov DWORD PTR [edi+352], eax
	mov eax, 786211301
	mov DWORD PTR [edi+356], eax
	mov eax, 87251563
	mov DWORD PTR [edi+360], eax
	mov eax, -120756437
	mov DWORD PTR [edi+364], eax
	mov eax, 65005688
	mov DWORD PTR [edi+368], eax
	mov eax, -1364605522
	mov DWORD PTR [edi+372], eax
	mov eax, 1632077553
	mov DWORD PTR [edi+376], eax
	mov eax, 0
	mov DWORD PTR [edi+380], eax
	mov eax, 1599175957
	mov DWORD PTR [edi+384], eax
	mov eax, 697596521
	mov DWORD PTR [edi+388], eax
	mov eax, 836124491
	mov DWORD PTR [edi+392], eax
	mov eax, -1412890791
	mov DWORD PTR [edi+396], eax
	mov eax, -646887338
	mov DWORD PTR [edi+400], eax
	mov eax, 1792106364
	mov DWORD PTR [edi+404], eax
	mov eax, -1310099103
	mov DWORD PTR [edi+408], eax
	mov eax, 0
	mov DWORD PTR [edi+412], eax
	mov eax, 0
	mov DWORD PTR [edi+416], eax
	mov eax, -1549543997
	mov DWORD PTR [edi+420], eax
	mov eax, -333261126
	mov DWORD PTR [edi+424], eax
	mov eax, 524750785
	mov DWORD PTR [edi+428], eax
	mov eax, 59741
	mov DWORD PTR [edi+432], eax
	mov eax, 0
	mov DWORD PTR [edi+436], eax
	mov eax, 0
	mov DWORD PTR [edi+440], eax
	mov eax, 0
	mov DWORD PTR [edi+444], eax
	mov eax, -1
	mov DWORD PTR [edi+448], eax
	mov eax, -1
	mov DWORD PTR [edi+452], eax
	mov eax, -1
	mov DWORD PTR [edi+456], eax
	mov eax, -2
	mov DWORD PTR [edi+460], eax
	mov eax, -1
	mov DWORD PTR [edi+464], eax
	mov eax, -1
	mov DWORD PTR [edi+468], eax
	mov eax, -1
	mov DWORD PTR [edi+472], eax
	mov eax, 0
	mov DWORD PTR [edi+476], eax
	mov eax, 1549543995
	mov DWORD PTR [edi+480], eax
	mov eax, 333261125
	mov DWORD PTR [edi+484], eax
	mov eax, -524750786
	mov DWORD PTR [edi+488], eax
	mov eax, -59742
	mov DWORD PTR [edi+492], eax
	mov eax, -1
	mov DWORD PTR [edi+496], eax
	mov eax, -1
	mov DWORD PTR [edi+500], eax
	mov eax, -1
	mov DWORD PTR [edi+504], eax
	mov eax, 0
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
	mov eax, 0
	mov DWORD PTR [edi+544], eax
	mov eax, -1
	mov DWORD PTR [edi+548], eax
	mov eax, -1
	mov DWORD PTR [edi+552], eax
	mov eax, -1
	mov DWORD PTR [edi+556], eax
	mov eax, 0
	mov DWORD PTR [edi+560], eax
	mov eax, 0
	mov DWORD PTR [edi+564], eax
	mov eax, 0
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
	mov eax, 1
	mov DWORD PTR [edi+1312], eax
	mov eax, -1
	mov DWORD PTR [edi+1316], eax
	mov eax, 0
	mov DWORD PTR [edi+1320], eax
	mov eax, -1
	mov DWORD PTR [edi+1324], eax
	mov eax, 0
	mov DWORD PTR [edi+1328], eax
	mov eax, -2
	mov DWORD PTR [edi+1332], eax
	mov eax, -1
	mov DWORD PTR [edi+1336], eax
	mov eax, 0
	mov DWORD PTR [edi+1340], eax
	mov eax, 1673550285
	mov DWORD PTR [edi+1344], eax
	mov eax, -412561930
	mov DWORD PTR [edi+1348], eax
	mov eax, -856681712
	mov DWORD PTR [edi+1352], eax
	mov eax, 276480755
	mov DWORD PTR [edi+1356], eax
	mov eax, -934117039
	mov DWORD PTR [edi+1360], eax
	mov eax, 1036958360
	mov DWORD PTR [edi+1364], eax
	mov eax, 2143301523
	mov DWORD PTR [edi+1368], eax
	mov eax, 0
	mov DWORD PTR [edi+1372], eax
	mov ebx, DWORD PTR [esp+8]
	add ebx, 1
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1144], eax
	mov eax, 0
	mov DWORD PTR [edi+1148], eax
	add ebx, 28
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1240], eax
	mov eax, 0
	mov DWORD PTR [edi+1244], eax
	mov ebx, DWORD PTR [esp+8]
	movzx edx, BYTE PTR [ebx]
	xor edx, 4
	sub edx, 1
	sbb edx, edx
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov edx, DWORD PTR [edi+1120]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+1124]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+1128]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+1132]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+1136]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+1140]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+1144]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+1148]
	sbb edx, DWORD PTR [edi+92]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov edx, DWORD PTR [edi+1216]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+1220]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+1224]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+1228]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+1232]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+1236]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+1240]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+1244]
	sbb edx, DWORD PTR [edi+92]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov eax, 1312
	mov ecx, 1120
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1312
	mov ecx, 1216
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1184
	mov ecx, 1184
	mov edx, 1248
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1152
	mov edx, 1376
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1376
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 256
	mov edx, 1376
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1376
	mov ecx, 1408
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1280
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1248
	mov edx, 1376
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1376]
	or edx, DWORD PTR [edi+1380]
	or edx, DWORD PTR [edi+1384]
	or edx, DWORD PTR [edi+1388]
	or edx, DWORD PTR [edi+1392]
	or edx, DWORD PTR [edi+1396]
	or edx, DWORD PTR [edi+1400]
	or edx, DWORD PTR [edi+1404]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov ecx, DWORD PTR [edi+1472]
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+1152]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1280], eax
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+1156]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1284], eax
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+1160]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1288], eax
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+1164]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1292], eax
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+1168]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1296], eax
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+1172]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1300], eax
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+1176]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1304], eax
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+1180]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1308], eax
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+1184]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1440], eax
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+1188]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1444], eax
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+1192]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1448], eax
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+1196]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1452], eax
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+1200]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+1204]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+1208]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+1212]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1468], eax
	mov ecx, DWORD PTR [edi+1472]
	mov ebx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+1216]
	and eax, 1
	or eax, 2
	and eax, ecx
	mov BYTE PTR [ebx], al
	mov eax, DWORD PTR [edi+1120]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+25], eax
	mov eax, DWORD PTR [edi+1124]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+21], eax
	mov eax, DWORD PTR [edi+1128]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+17], eax
	mov eax, DWORD PTR [edi+1132]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+13], eax
	mov eax, DWORD PTR [edi+1136]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+9], eax
	mov eax, DWORD PTR [edi+1140]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+5], eax
	mov eax, DWORD PTR [edi+1144]
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
	ret
	.p2align 6

vg_ec_p224_decompress_public_key:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1080], eax
	mov eax, 0
	mov DWORD PTR [edi+1084], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1112], eax
	mov eax, 0
	mov DWORD PTR [edi+1116], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1144], eax
	mov eax, 0
	mov DWORD PTR [edi+1148], eax
	mov eax, 1
	mov DWORD PTR [edi+64], eax
	mov eax, 0
	mov DWORD PTR [edi+68], eax
	mov eax, 0
	mov DWORD PTR [edi+72], eax
	mov eax, -1
	mov DWORD PTR [edi+76], eax
	mov eax, -1
	mov DWORD PTR [edi+80], eax
	mov eax, -1
	mov DWORD PTR [edi+84], eax
	mov eax, -1
	mov DWORD PTR [edi+88], eax
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov eax, 1549543997
	mov DWORD PTR [edi+96], eax
	mov eax, 333261125
	mov DWORD PTR [edi+100], eax
	mov eax, -524750786
	mov DWORD PTR [edi+104], eax
	mov eax, -59742
	mov DWORD PTR [edi+108], eax
	mov eax, -1
	mov DWORD PTR [edi+112], eax
	mov eax, -1
	mov DWORD PTR [edi+116], eax
	mov eax, -1
	mov DWORD PTR [edi+120], eax
	mov eax, 0
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
	mov eax, 0
	mov DWORD PTR [edi+224], eax
	mov eax, -1
	mov DWORD PTR [edi+228], eax
	mov eax, -1
	mov DWORD PTR [edi+232], eax
	mov eax, -1
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
	mov eax, 3
	mov DWORD PTR [edi+260], eax
	mov eax, 0
	mov DWORD PTR [edi+264], eax
	mov eax, -1
	mov DWORD PTR [edi+268], eax
	mov eax, -4
	mov DWORD PTR [edi+272], eax
	mov eax, -1
	mov DWORD PTR [edi+276], eax
	mov eax, -1
	mov DWORD PTR [edi+280], eax
	mov eax, 0
	mov DWORD PTR [edi+284], eax
	mov eax, 725683558
	mov DWORD PTR [edi+288], eax
	mov eax, -1237685789
	mov DWORD PTR [edi+292], eax
	mov eax, 1724922162
	mov DWORD PTR [edi+296], eax
	mov eax, 829442268
	mov DWORD PTR [edi+300], eax
	mov eax, 1492616179
	mov DWORD PTR [edi+304], eax
	mov eax, -1184092214
	mov DWORD PTR [edi+308], eax
	mov eax, 2134937273
	mov DWORD PTR [edi+312], eax
	mov eax, 0
	mov DWORD PTR [edi+316], eax
	mov eax, 1829391082
	mov DWORD PTR [edi+320], eax
	mov eax, -1131392474
	mov DWORD PTR [edi+324], eax
	mov eax, 1612234666
	mov DWORD PTR [edi+328], eax
	mov eax, -2061134026
	mov DWORD PTR [edi+332], eax
	mov eax, -110367739
	mov DWORD PTR [edi+336], eax
	mov eax, 1842589595
	mov DWORD PTR [edi+340], eax
	mov eax, -1575264672
	mov DWORD PTR [edi+344], eax
	mov eax, 0
	mov DWORD PTR [edi+348], eax
	mov eax, -269226520
	mov DWORD PTR [edi+352], eax
	mov eax, 786211301
	mov DWORD PTR [edi+356], eax
	mov eax, 87251563
	mov DWORD PTR [edi+360], eax
	mov eax, -120756437
	mov DWORD PTR [edi+364], eax
	mov eax, 65005688
	mov DWORD PTR [edi+368], eax
	mov eax, -1364605522
	mov DWORD PTR [edi+372], eax
	mov eax, 1632077553
	mov DWORD PTR [edi+376], eax
	mov eax, 0
	mov DWORD PTR [edi+380], eax
	mov eax, 1599175957
	mov DWORD PTR [edi+384], eax
	mov eax, 697596521
	mov DWORD PTR [edi+388], eax
	mov eax, 836124491
	mov DWORD PTR [edi+392], eax
	mov eax, -1412890791
	mov DWORD PTR [edi+396], eax
	mov eax, -646887338
	mov DWORD PTR [edi+400], eax
	mov eax, 1792106364
	mov DWORD PTR [edi+404], eax
	mov eax, -1310099103
	mov DWORD PTR [edi+408], eax
	mov eax, 0
	mov DWORD PTR [edi+412], eax
	mov eax, 0
	mov DWORD PTR [edi+416], eax
	mov eax, -1549543997
	mov DWORD PTR [edi+420], eax
	mov eax, -333261126
	mov DWORD PTR [edi+424], eax
	mov eax, 524750785
	mov DWORD PTR [edi+428], eax
	mov eax, 59741
	mov DWORD PTR [edi+432], eax
	mov eax, 0
	mov DWORD PTR [edi+436], eax
	mov eax, 0
	mov DWORD PTR [edi+440], eax
	mov eax, 0
	mov DWORD PTR [edi+444], eax
	mov eax, -1
	mov DWORD PTR [edi+448], eax
	mov eax, -1
	mov DWORD PTR [edi+452], eax
	mov eax, -1
	mov DWORD PTR [edi+456], eax
	mov eax, -2
	mov DWORD PTR [edi+460], eax
	mov eax, -1
	mov DWORD PTR [edi+464], eax
	mov eax, -1
	mov DWORD PTR [edi+468], eax
	mov eax, -1
	mov DWORD PTR [edi+472], eax
	mov eax, 0
	mov DWORD PTR [edi+476], eax
	mov eax, 1549543995
	mov DWORD PTR [edi+480], eax
	mov eax, 333261125
	mov DWORD PTR [edi+484], eax
	mov eax, -524750786
	mov DWORD PTR [edi+488], eax
	mov eax, -59742
	mov DWORD PTR [edi+492], eax
	mov eax, -1
	mov DWORD PTR [edi+496], eax
	mov eax, -1
	mov DWORD PTR [edi+500], eax
	mov eax, -1
	mov DWORD PTR [edi+504], eax
	mov eax, 0
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
	mov eax, 0
	mov DWORD PTR [edi+544], eax
	mov eax, -1
	mov DWORD PTR [edi+548], eax
	mov eax, -1
	mov DWORD PTR [edi+552], eax
	mov eax, -1
	mov DWORD PTR [edi+556], eax
	mov eax, 0
	mov DWORD PTR [edi+560], eax
	mov eax, 0
	mov DWORD PTR [edi+564], eax
	mov eax, 0
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
	mov eax, 1
	mov DWORD PTR [edi+1312], eax
	mov eax, -1
	mov DWORD PTR [edi+1316], eax
	mov eax, 0
	mov DWORD PTR [edi+1320], eax
	mov eax, -1
	mov DWORD PTR [edi+1324], eax
	mov eax, 0
	mov DWORD PTR [edi+1328], eax
	mov eax, -2
	mov DWORD PTR [edi+1332], eax
	mov eax, -1
	mov DWORD PTR [edi+1336], eax
	mov eax, 0
	mov DWORD PTR [edi+1340], eax
	mov eax, 1673550285
	mov DWORD PTR [edi+1344], eax
	mov eax, -412561930
	mov DWORD PTR [edi+1348], eax
	mov eax, -856681712
	mov DWORD PTR [edi+1352], eax
	mov eax, 276480755
	mov DWORD PTR [edi+1356], eax
	mov eax, -934117039
	mov DWORD PTR [edi+1360], eax
	mov eax, 1036958360
	mov DWORD PTR [edi+1364], eax
	mov eax, 2143301523
	mov DWORD PTR [edi+1368], eax
	mov eax, 0
	mov DWORD PTR [edi+1372], eax
	mov ebx, DWORD PTR [esp+8]
	add ebx, 1
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1144], eax
	mov eax, 0
	mov DWORD PTR [edi+1148], eax
	mov ebx, DWORD PTR [esp+8]
	movzx edx, BYTE PTR [ebx]
	mov DWORD PTR [edi+1088], edx
	or edx, 1
	xor edx, 3
	sub edx, 1
	sbb edx, edx
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov edx, DWORD PTR [edi+1120]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+1124]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+1128]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+1132]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+1136]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+1140]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+1144]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+1148]
	sbb edx, DWORD PTR [edi+92]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov eax, 1312
	mov ecx, 1120
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1152
	mov edx, 1376
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1376
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 256
	mov edx, 1376
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1376
	mov ecx, 1408
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1280
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 0
	mov DWORD PTR [edi+448], eax
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov eax, 0
	mov DWORD PTR [edi+456], eax
	mov eax, -2147483648
	mov DWORD PTR [edi+460], eax
	mov eax, 0
	mov DWORD PTR [edi+464], eax
	mov eax, 0
	mov DWORD PTR [edi+468], eax
	mov eax, 0
	mov DWORD PTR [edi+472], eax
	mov eax, 0
	mov DWORD PTR [edi+476], eax
	mov esi, 32
20:
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
	jne 20b
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+1020], eax
	mov esi, 256
21:
	sub esi, 1
	mov eax, 992
	mov ecx, 992
	mov edx, 992
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 992
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4356]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+992]
	mov edx, DWORD PTR [edi+1024]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+996]
	mov edx, DWORD PTR [edi+1028]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+1000]
	mov edx, DWORD PTR [edi+1032]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+1004]
	mov edx, DWORD PTR [edi+1036]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [edi+1008]
	mov edx, DWORD PTR [edi+1040]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+1012]
	mov edx, DWORD PTR [edi+1044]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+1016]
	mov edx, DWORD PTR [edi+1048]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+1020]
	mov edx, DWORD PTR [edi+1052]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1020], eax
	test esi, esi
	jne 21b
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [edi+960], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [edi+964], eax
	mov eax, DWORD PTR [edi+1000]
	mov DWORD PTR [edi+968], eax
	mov eax, DWORD PTR [edi+1004]
	mov DWORD PTR [edi+972], eax
	mov eax, DWORD PTR [edi+1008]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+1012]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [edi+1016]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [edi+1020]
	mov DWORD PTR [edi+988], eax
	mov eax, -1
	mov DWORD PTR [edi+448], eax
	mov eax, -1
	mov DWORD PTR [edi+452], eax
	mov eax, -1
	mov DWORD PTR [edi+456], eax
	mov eax, -1
	mov DWORD PTR [edi+460], eax
	mov eax, 0
	mov DWORD PTR [edi+464], eax
	mov eax, 0
	mov DWORD PTR [edi+468], eax
	mov eax, 0
	mov DWORD PTR [edi+472], eax
	mov eax, 0
	mov DWORD PTR [edi+476], eax
	mov esi, 32
22:
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
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+1020], eax
	mov esi, 256
23:
	sub esi, 1
	mov eax, 992
	mov ecx, 992
	mov edx, 992
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 992
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4616]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+992]
	mov edx, DWORD PTR [edi+1024]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+996]
	mov edx, DWORD PTR [edi+1028]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+1000]
	mov edx, DWORD PTR [edi+1032]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+1004]
	mov edx, DWORD PTR [edi+1036]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [edi+1008]
	mov edx, DWORD PTR [edi+1040]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+1012]
	mov edx, DWORD PTR [edi+1044]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+1016]
	mov edx, DWORD PTR [edi+1048]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+1020]
	mov edx, DWORD PTR [edi+1052]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1020], eax
	test esi, esi
	jne 23b
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [edi+1000]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [edi+1004]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [edi+1008]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [edi+1012]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [edi+1016]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [edi+1020]
	mov DWORD PTR [edi+828], eax
	mov eax, DWORD PTR [edi+960]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+964]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+968]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+972]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [edi+1020], eax
	mov eax, 1591901292
	mov DWORD PTR [edi+832], eax
	mov eax, 390148536
	mov DWORD PTR [edi+836], eax
	mov eax, -2039733701
	mov DWORD PTR [edi+840], eax
	mov eax, 2020195933
	mov DWORD PTR [edi+844], eax
	mov eax, -577675701
	mov DWORD PTR [edi+848], eax
	mov eax, 1832790768
	mov DWORD PTR [edi+852], eax
	mov eax, -1558504028
	mov DWORD PTR [edi+856], eax
	mov eax, 0
	mov DWORD PTR [edi+860], eax
	mov eax, 95
	mov DWORD PTR [edi+864], eax
24:
	mov eax, DWORD PTR [edi+800]
	mov DWORD PTR [edi+896], eax
	mov eax, DWORD PTR [edi+804]
	mov DWORD PTR [edi+900], eax
	mov eax, DWORD PTR [edi+808]
	mov DWORD PTR [edi+904], eax
	mov eax, DWORD PTR [edi+812]
	mov DWORD PTR [edi+908], eax
	mov eax, DWORD PTR [edi+816]
	mov DWORD PTR [edi+912], eax
	mov eax, DWORD PTR [edi+820]
	mov DWORD PTR [edi+916], eax
	mov eax, DWORD PTR [edi+824]
	mov DWORD PTR [edi+920], eax
	mov eax, DWORD PTR [edi+828]
	mov DWORD PTR [edi+924], eax
	mov esi, DWORD PTR [edi+864]
	sub esi, 1
	test esi, esi
	je 25f
27:
	mov eax, 896
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	sub esi, 1
	test esi, esi
	jne 27b
	jmp 26f
25:
26:
	mov eax, 224
	mov ecx, 896
	mov edx, 1248
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1248]
	or edx, DWORD PTR [edi+1252]
	or edx, DWORD PTR [edi+1256]
	or edx, DWORD PTR [edi+1260]
	or edx, DWORD PTR [edi+1264]
	or edx, DWORD PTR [edi+1268]
	or edx, DWORD PTR [edi+1272]
	or edx, DWORD PTR [edi+1276]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, 0
	sub eax, edx
	mov edx, eax
	sub edx, 1
	mov ecx, edx
	mov eax, DWORD PTR [edi+832]
	mov edx, DWORD PTR [edi+224]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [edi+836]
	mov edx, DWORD PTR [edi+228]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [edi+840]
	mov edx, DWORD PTR [edi+232]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+936], eax
	mov eax, DWORD PTR [edi+844]
	mov edx, DWORD PTR [edi+236]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+940], eax
	mov eax, DWORD PTR [edi+848]
	mov edx, DWORD PTR [edi+240]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+944], eax
	mov eax, DWORD PTR [edi+852]
	mov edx, DWORD PTR [edi+244]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+948], eax
	mov eax, DWORD PTR [edi+856]
	mov edx, DWORD PTR [edi+248]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+952], eax
	mov eax, DWORD PTR [edi+860]
	mov edx, DWORD PTR [edi+252]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+956], eax
	mov eax, 928
	mov ecx, 992
	mov edx, 992
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 800
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 832
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [edi+864]
	sub esi, 1
	mov DWORD PTR [edi+864], esi
	test esi, esi
	jne 24b
	mov eax, 192
	mov ecx, 992
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 160
	mov edx, 1248
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1216]
	mov ecx, DWORD PTR [edi+1088]
	xor ecx, eax
	and ecx, 1
	mov edx, 0
	sub edx, ecx
	mov ecx, edx
	mov eax, DWORD PTR [edi+1216]
	mov edx, DWORD PTR [edi+1248]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [edi+1220]
	mov edx, DWORD PTR [edi+1252]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [edi+1224]
	mov edx, DWORD PTR [edi+1256]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+1228]
	mov edx, DWORD PTR [edi+1260]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+1232]
	mov edx, DWORD PTR [edi+1264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+1236]
	mov edx, DWORD PTR [edi+1268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+1240]
	mov edx, DWORD PTR [edi+1272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+1244]
	mov edx, DWORD PTR [edi+1276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1244], eax
	mov eax, 1312
	mov ecx, 1216
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1184
	mov ecx, 1184
	mov edx, 1376
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1376
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1280]
	or edx, DWORD PTR [edi+1284]
	or edx, DWORD PTR [edi+1288]
	or edx, DWORD PTR [edi+1292]
	or edx, DWORD PTR [edi+1296]
	or edx, DWORD PTR [edi+1300]
	or edx, DWORD PTR [edi+1304]
	or edx, DWORD PTR [edi+1308]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov eax, DWORD PTR [edi+1216]
	mov ecx, DWORD PTR [edi+1088]
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
	mov eax, DWORD PTR [edi+1472]
	and eax, edx
	mov DWORD PTR [edi+1472], eax
	mov ecx, DWORD PTR [edi+1472]
	mov ebx, DWORD PTR [esp+4]
	mov eax, 4
	and eax, ecx
	mov BYTE PTR [ebx], al
	mov eax, DWORD PTR [edi+1120]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+25], eax
	mov eax, DWORD PTR [edi+1124]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+21], eax
	mov eax, DWORD PTR [edi+1128]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+17], eax
	mov eax, DWORD PTR [edi+1132]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+13], eax
	mov eax, DWORD PTR [edi+1136]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+9], eax
	mov eax, DWORD PTR [edi+1140]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+5], eax
	mov eax, DWORD PTR [edi+1144]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+1], eax
	mov eax, DWORD PTR [edi+1216]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+53], eax
	mov eax, DWORD PTR [edi+1220]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+49], eax
	mov eax, DWORD PTR [edi+1224]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+45], eax
	mov eax, DWORD PTR [edi+1228]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+41], eax
	mov eax, DWORD PTR [edi+1232]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+37], eax
	mov eax, DWORD PTR [edi+1236]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+33], eax
	mov eax, DWORD PTR [edi+1240]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+29], eax
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	ret
	.p2align 6
