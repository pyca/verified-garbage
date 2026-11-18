// The functions of `src/x448.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x448_exchange:
	lea esp, [esp-16]
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp+12], eax
	call {vg_x448}
	lea esp, [esp+16]
	mov edx, DWORD PTR [esp+4]
	mov ecx, 0
	movzx eax, BYTE PTR [edx]
	or ecx, eax
	movzx eax, BYTE PTR [edx+1]
	or ecx, eax
	movzx eax, BYTE PTR [edx+2]
	or ecx, eax
	movzx eax, BYTE PTR [edx+3]
	or ecx, eax
	movzx eax, BYTE PTR [edx+4]
	or ecx, eax
	movzx eax, BYTE PTR [edx+5]
	or ecx, eax
	movzx eax, BYTE PTR [edx+6]
	or ecx, eax
	movzx eax, BYTE PTR [edx+7]
	or ecx, eax
	movzx eax, BYTE PTR [edx+8]
	or ecx, eax
	movzx eax, BYTE PTR [edx+9]
	or ecx, eax
	movzx eax, BYTE PTR [edx+10]
	or ecx, eax
	movzx eax, BYTE PTR [edx+11]
	or ecx, eax
	movzx eax, BYTE PTR [edx+12]
	or ecx, eax
	movzx eax, BYTE PTR [edx+13]
	or ecx, eax
	movzx eax, BYTE PTR [edx+14]
	or ecx, eax
	movzx eax, BYTE PTR [edx+15]
	or ecx, eax
	movzx eax, BYTE PTR [edx+16]
	or ecx, eax
	movzx eax, BYTE PTR [edx+17]
	or ecx, eax
	movzx eax, BYTE PTR [edx+18]
	or ecx, eax
	movzx eax, BYTE PTR [edx+19]
	or ecx, eax
	movzx eax, BYTE PTR [edx+20]
	or ecx, eax
	movzx eax, BYTE PTR [edx+21]
	or ecx, eax
	movzx eax, BYTE PTR [edx+22]
	or ecx, eax
	movzx eax, BYTE PTR [edx+23]
	or ecx, eax
	movzx eax, BYTE PTR [edx+24]
	or ecx, eax
	movzx eax, BYTE PTR [edx+25]
	or ecx, eax
	movzx eax, BYTE PTR [edx+26]
	or ecx, eax
	movzx eax, BYTE PTR [edx+27]
	or ecx, eax
	movzx eax, BYTE PTR [edx+28]
	or ecx, eax
	movzx eax, BYTE PTR [edx+29]
	or ecx, eax
	movzx eax, BYTE PTR [edx+30]
	or ecx, eax
	movzx eax, BYTE PTR [edx+31]
	or ecx, eax
	movzx eax, BYTE PTR [edx+32]
	or ecx, eax
	movzx eax, BYTE PTR [edx+33]
	or ecx, eax
	movzx eax, BYTE PTR [edx+34]
	or ecx, eax
	movzx eax, BYTE PTR [edx+35]
	or ecx, eax
	movzx eax, BYTE PTR [edx+36]
	or ecx, eax
	movzx eax, BYTE PTR [edx+37]
	or ecx, eax
	movzx eax, BYTE PTR [edx+38]
	or ecx, eax
	movzx eax, BYTE PTR [edx+39]
	or ecx, eax
	movzx eax, BYTE PTR [edx+40]
	or ecx, eax
	movzx eax, BYTE PTR [edx+41]
	or ecx, eax
	movzx eax, BYTE PTR [edx+42]
	or ecx, eax
	movzx eax, BYTE PTR [edx+43]
	or ecx, eax
	movzx eax, BYTE PTR [edx+44]
	or ecx, eax
	movzx eax, BYTE PTR [edx+45]
	or ecx, eax
	movzx eax, BYTE PTR [edx+46]
	or ecx, eax
	movzx eax, BYTE PTR [edx+47]
	or ecx, eax
	movzx eax, BYTE PTR [edx+48]
	or ecx, eax
	movzx eax, BYTE PTR [edx+49]
	or ecx, eax
	movzx eax, BYTE PTR [edx+50]
	or ecx, eax
	movzx eax, BYTE PTR [edx+51]
	or ecx, eax
	movzx eax, BYTE PTR [edx+52]
	or ecx, eax
	movzx eax, BYTE PTR [edx+53]
	or ecx, eax
	movzx eax, BYTE PTR [edx+54]
	or ecx, eax
	movzx eax, BYTE PTR [edx+55]
	or ecx, eax
	sub ecx, 1
	shr ecx, 31
	xor ecx, 1
	mov eax, ecx
	ret
	.p2align 6

vg_x448_base:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebp, edi
	add ebp, 64
	mov ebx, 0
	mov eax, 704
20:
	mov DWORD PTR [ebp], ebx
	add ebp, 4
	sub eax, 1
	jne 20b
	mov ebp, edi
	add ebp, 64
	mov eax, 1
	mov DWORD PTR [ebp+128], eax
	mov eax, 1
	mov DWORD PTR [ebp+256], eax
	mov eax, 49246
	mov DWORD PTR [ebp+1024], eax
	mov eax, 50956
	mov DWORD PTR [ebp+1028], eax
	mov eax, 43051
	mov DWORD PTR [ebp+1032], eax
	mov eax, 9766
	mov DWORD PTR [ebp+1036], eax
	mov eax, 37774
	mov DWORD PTR [ebp+1040], eax
	mov eax, 35584
	mov DWORD PTR [ebp+1044], eax
	mov eax, 32993
	mov DWORD PTR [ebp+1048], eax
	mov eax, 17211
	mov DWORD PTR [ebp+1052], eax
	mov eax, 25873
	mov DWORD PTR [ebp+1056], eax
	mov eax, 10934
	mov DWORD PTR [ebp+1060], eax
	mov eax, 6903
	mov DWORD PTR [ebp+1064], eax
	mov eax, 4782
	mov DWORD PTR [ebp+1068], eax
	mov eax, 42084
	mov DWORD PTR [ebp+1072], eax
	mov eax, 41939
	mov DWORD PTR [ebp+1076], eax
	mov eax, 58148
	mov DWORD PTR [ebp+1080], eax
	mov eax, 60013
	mov DWORD PTR [ebp+1084], eax
	mov eax, 5991
	mov DWORD PTR [ebp+1088], eax
	mov eax, 18191
	mov DWORD PTR [ebp+1092], eax
	mov eax, 25968
	mov DWORD PTR [ebp+1096], eax
	mov eax, 40468
	mov DWORD PTR [ebp+1100], eax
	mov eax, 14042
	mov DWORD PTR [ebp+1104], eax
	mov eax, 8895
	mov DWORD PTR [ebp+1108], eax
	mov eax, 5542
	mov DWORD PTR [ebp+1112], eax
	mov eax, 8733
	mov DWORD PTR [ebp+1116], eax
	mov eax, 3565
	mov DWORD PTR [ebp+1120], eax
	mov eax, 27629
	mov DWORD PTR [ebp+1124], eax
	mov eax, 28870
	mov DWORD PTR [ebp+1128], eax
	mov eax, 20249
	mov DWORD PTR [ebp+1132], eax
	mov eax, 64020
	mov DWORD PTR [ebp+1152], eax
	mov eax, 62000
	mov DWORD PTR [ebp+1156], eax
	mov eax, 31067
	mov DWORD PTR [ebp+1160], eax
	mov eax, 38920
	mov DWORD PTR [ebp+1164], eax
	mov eax, 51373
	mov DWORD PTR [ebp+1168], eax
	mov eax, 20183
	mov DWORD PTR [ebp+1172], eax
	mov eax, 4908
	mov DWORD PTR [ebp+1176], eax
	mov eax, 64957
	mov DWORD PTR [ebp+1180], eax
	mov eax, 14788
	mov DWORD PTR [ebp+1184], eax
	mov eax, 59004
	mov DWORD PTR [ebp+1188], eax
	mov eax, 65308
	mov DWORD PTR [ebp+1192], eax
	mov eax, 15059
	mov DWORD PTR [ebp+1196], eax
	mov eax, 49879
	mov DWORD PTR [ebp+1200], eax
	mov eax, 1440
	mov DWORD PTR [ebp+1204], eax
	mov eax, 39966
	mov DWORD PTR [ebp+1208], eax
	mov eax, 34680
	mov DWORD PTR [ebp+1212], eax
	mov eax, 38976
	mov DWORD PTR [ebp+1216], eax
	mov eax, 27811
	mov DWORD PTR [ebp+1220], eax
	mov eax, 29555
	mov DWORD PTR [ebp+1224], eax
	mov eax, 19434
	mov DWORD PTR [ebp+1228], eax
	mov eax, 51042
	mov DWORD PTR [ebp+1232], eax
	mov eax, 22217
	mov DWORD PTR [ebp+1236], eax
	mov eax, 8247
	mov DWORD PTR [ebp+1240], eax
	mov eax, 34934
	mov DWORD PTR [ebp+1244], eax
	mov eax, 48164
	mov DWORD PTR [ebp+1248], eax
	mov eax, 28342
	mov DWORD PTR [ebp+1252], eax
	mov eax, 18033
	mov DWORD PTR [ebp+1256], eax
	mov eax, 26943
	mov DWORD PTR [ebp+1260], eax
	mov eax, 1
	mov DWORD PTR [ebp+1280], eax
	mov eax, 26454
	mov DWORD PTR [ebp+1408], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1412], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1416], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1420], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1424], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1428], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1432], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1436], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1440], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1444], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1448], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1452], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1456], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1460], eax
	mov eax, 65534
	mov DWORD PTR [ebp+1464], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1468], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1472], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1476], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1480], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1484], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1488], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1492], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1496], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1500], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1504], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1508], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1512], eax
	mov eax, 65535
	mov DWORD PTR [ebp+1516], eax
	mov edx, 0
	mov BYTE PTR [edi+3520], dl
	mov BYTE PTR [edi+3521], dl
	mov BYTE PTR [edi+3522], dl
	mov BYTE PTR [edi+3523], dl
	mov BYTE PTR [edi+3524], dl
	mov BYTE PTR [edi+3525], dl
	mov BYTE PTR [edi+3526], dl
	mov BYTE PTR [edi+3527], dl
	mov esi, DWORD PTR [esp+8]
	mov ebp, edi
	mov ecx, 56
21:
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
	jne 21b
	mov edx, 0
	mov BYTE PTR [edi+3072], dl
	mov BYTE PTR [edi+3073], dl
	mov edx, 1
	mov BYTE PTR [edi+3519], dl
	mov esi, 114
22:
	sub esi, 1
	mov eax, 1600
	mov ecx, 64
	mov edx, 192
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 64
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 192
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 320
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 2112
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 1984
	mov edx, 2240
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 1600
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 64
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
	mov eax, 2496
	mov ecx, 1728
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 192
	mov ecx, 1984
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
	mov eax, 320
	mov ecx, 1984
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
	mov ebp, edi
	add ebp, esi
	movzx ecx, BYTE PTR [ebp+3414]
	movzx eax, BYTE PTR [ebp+3300]
	add ecx, ecx
	add ecx, eax
	movzx eax, BYTE PTR [ebp+3186]
	add ecx, ecx
	add ecx, eax
	movzx eax, BYTE PTR [ebp+3072]
	add ecx, ecx
	add ecx, eax
	mov eax, 0
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
	mov eax, ecx
	xor eax, 0
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1144], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1148], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1152], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1156], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1160], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1164], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1168], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1172], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1176], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1180], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+1184], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+1188], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1192], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1196], eax
	mov eax, 1
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1272], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1276], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1280], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1284], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1288], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1292], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1296], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1300], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1304], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1308], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1312], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1316], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1320], eax
	mov eax, 0
	and eax, ebx
	or eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1324], eax
	mov eax, ecx
	xor eax, 1
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 49246
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 50956
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 43051
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 9766
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 37774
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 35584
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 32993
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 17211
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 25873
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 10934
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 6903
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 4782
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 42084
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 41939
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 58148
	and eax, ebx
	or eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1144], eax
	mov eax, 60013
	and eax, ebx
	or eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1148], eax
	mov eax, 5991
	and eax, ebx
	or eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1152], eax
	mov eax, 18191
	and eax, ebx
	or eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1156], eax
	mov eax, 25968
	and eax, ebx
	or eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1160], eax
	mov eax, 40468
	and eax, ebx
	or eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1164], eax
	mov eax, 14042
	and eax, ebx
	or eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1168], eax
	mov eax, 8895
	and eax, ebx
	or eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1172], eax
	mov eax, 5542
	and eax, ebx
	or eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1176], eax
	mov eax, 8733
	and eax, ebx
	or eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1180], eax
	mov eax, 3565
	and eax, ebx
	or eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+1184], eax
	mov eax, 27629
	and eax, ebx
	or eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+1188], eax
	mov eax, 28870
	and eax, ebx
	or eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1192], eax
	mov eax, 20249
	and eax, ebx
	or eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1196], eax
	mov eax, 64020
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 62000
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 31067
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 38920
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 51373
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 20183
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 4908
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 64957
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 14788
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 59004
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 65308
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 15059
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 49879
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 1440
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 39966
	and eax, ebx
	or eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1272], eax
	mov eax, 34680
	and eax, ebx
	or eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1276], eax
	mov eax, 38976
	and eax, ebx
	or eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1280], eax
	mov eax, 27811
	and eax, ebx
	or eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1284], eax
	mov eax, 29555
	and eax, ebx
	or eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1288], eax
	mov eax, 19434
	and eax, ebx
	or eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1292], eax
	mov eax, 51042
	and eax, ebx
	or eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1296], eax
	mov eax, 22217
	and eax, ebx
	or eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1300], eax
	mov eax, 8247
	and eax, ebx
	or eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1304], eax
	mov eax, 34934
	and eax, ebx
	or eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1308], eax
	mov eax, 48164
	and eax, ebx
	or eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1312], eax
	mov eax, 28342
	and eax, ebx
	or eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1316], eax
	mov eax, 18033
	and eax, ebx
	or eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1320], eax
	mov eax, 26943
	and eax, ebx
	or eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1324], eax
	mov eax, ecx
	xor eax, 2
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 25176
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 36071
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 39032
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 30115
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 38073
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 53364
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 12337
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 57314
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 8259
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 28005
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 60490
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 17409
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 33947
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 56090
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 48076
	and eax, ebx
	or eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1144], eax
	mov eax, 48360
	and eax, ebx
	or eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1148], eax
	mov eax, 7867
	and eax, ebx
	or eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1152], eax
	mov eax, 40696
	and eax, ebx
	or eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1156], eax
	mov eax, 28414
	and eax, ebx
	or eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1160], eax
	mov eax, 54385
	and eax, ebx
	or eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1164], eax
	mov eax, 37757
	and eax, ebx
	or eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1168], eax
	mov eax, 24268
	and eax, ebx
	or eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1172], eax
	mov eax, 3832
	and eax, ebx
	or eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1176], eax
	mov eax, 6453
	and eax, ebx
	or eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1180], eax
	mov eax, 15260
	and eax, ebx
	or eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+1184], eax
	mov eax, 5159
	and eax, ebx
	or eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+1188], eax
	mov eax, 37666
	and eax, ebx
	or eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1192], eax
	mov eax, 9741
	and eax, ebx
	or eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1196], eax
	mov eax, 61859
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 59259
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 32289
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 46877
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 21582
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 26778
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 6557
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 60752
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 6476
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 42388
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 43677
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 41134
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 3048
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 29094
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 15185
	and eax, ebx
	or eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1272], eax
	mov eax, 57965
	and eax, ebx
	or eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1276], eax
	mov eax, 14858
	and eax, ebx
	or eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1280], eax
	mov eax, 10264
	and eax, ebx
	or eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1284], eax
	mov eax, 57239
	and eax, ebx
	or eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1288], eax
	mov eax, 30376
	and eax, ebx
	or eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1292], eax
	mov eax, 18929
	and eax, ebx
	or eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1296], eax
	mov eax, 1652
	and eax, ebx
	or eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1300], eax
	mov eax, 58147
	and eax, ebx
	or eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1304], eax
	mov eax, 17270
	and eax, ebx
	or eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1308], eax
	mov eax, 7284
	and eax, ebx
	or eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1312], eax
	mov eax, 9556
	and eax, ebx
	or eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1316], eax
	mov eax, 8622
	and eax, ebx
	or eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1320], eax
	mov eax, 45771
	and eax, ebx
	or eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1324], eax
	mov eax, ecx
	xor eax, 3
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 3863
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 45239
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 19666
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 41082
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 56238
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 12473
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 2206
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 4629
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 38784
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 37758
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 61242
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 57100
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 48971
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 50456
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 62333
	and eax, ebx
	or eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1144], eax
	mov eax, 58120
	and eax, ebx
	or eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1148], eax
	mov eax, 39350
	and eax, ebx
	or eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1152], eax
	mov eax, 48651
	and eax, ebx
	or eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1156], eax
	mov eax, 23102
	and eax, ebx
	or eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1160], eax
	mov eax, 32708
	and eax, ebx
	or eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1164], eax
	mov eax, 62939
	and eax, ebx
	or eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1168], eax
	mov eax, 3232
	and eax, ebx
	or eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1172], eax
	mov eax, 53089
	and eax, ebx
	or eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1176], eax
	mov eax, 15782
	and eax, ebx
	or eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1180], eax
	mov eax, 40722
	and eax, ebx
	or eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+1184], eax
	mov eax, 47276
	and eax, ebx
	or eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+1188], eax
	mov eax, 57867
	and eax, ebx
	or eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1192], eax
	mov eax, 53033
	and eax, ebx
	or eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1196], eax
	mov eax, 54515
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 47117
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 48322
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 10127
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 57271
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 63638
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 23260
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 38211
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 43633
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 31930
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 37811
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 43664
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 8640
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 35006
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 17527
	and eax, ebx
	or eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1272], eax
	mov eax, 53089
	and eax, ebx
	or eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1276], eax
	mov eax, 14390
	and eax, ebx
	or eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1280], eax
	mov eax, 60799
	and eax, ebx
	or eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1284], eax
	mov eax, 29917
	and eax, ebx
	or eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1288], eax
	mov eax, 51534
	and eax, ebx
	or eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1292], eax
	mov eax, 34474
	and eax, ebx
	or eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1296], eax
	mov eax, 51647
	and eax, ebx
	or eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1300], eax
	mov eax, 28312
	and eax, ebx
	or eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1304], eax
	mov eax, 47721
	and eax, ebx
	or eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1308], eax
	mov eax, 14106
	and eax, ebx
	or eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1312], eax
	mov eax, 46075
	and eax, ebx
	or eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1316], eax
	mov eax, 10213
	and eax, ebx
	or eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1320], eax
	mov eax, 10768
	and eax, ebx
	or eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1324], eax
	mov eax, ecx
	xor eax, 4
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 46688
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 30094
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 26984
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 19447
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 13802
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 64043
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 30682
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 4123
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 3746
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 19844
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 1381
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 37699
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 4145
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 41463
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 14784
	and eax, ebx
	or eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1144], eax
	mov eax, 52486
	and eax, ebx
	or eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1148], eax
	mov eax, 56424
	and eax, ebx
	or eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1152], eax
	mov eax, 57336
	and eax, ebx
	or eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1156], eax
	mov eax, 24575
	and eax, ebx
	or eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1160], eax
	mov eax, 2997
	and eax, ebx
	or eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1164], eax
	mov eax, 645
	and eax, ebx
	or eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1168], eax
	mov eax, 47110
	and eax, ebx
	or eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1172], eax
	mov eax, 773
	and eax, ebx
	or eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1176], eax
	mov eax, 24651
	and eax, ebx
	or eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1180], eax
	mov eax, 27142
	and eax, ebx
	or eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+1184], eax
	mov eax, 30337
	and eax, ebx
	or eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+1188], eax
	mov eax, 26515
	and eax, ebx
	or eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1192], eax
	mov eax, 1081
	and eax, ebx
	or eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1196], eax
	mov eax, 29333
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 4962
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 31609
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 40931
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 34266
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 1847
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 24487
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 28704
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 24288
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 22302
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 5435
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 41513
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 58495
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 64743
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 50927
	and eax, ebx
	or eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1272], eax
	mov eax, 59718
	and eax, ebx
	or eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1276], eax
	mov eax, 679
	and eax, ebx
	or eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1280], eax
	mov eax, 50557
	and eax, ebx
	or eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1284], eax
	mov eax, 1101
	and eax, ebx
	or eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1288], eax
	mov eax, 13686
	and eax, ebx
	or eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1292], eax
	mov eax, 35515
	and eax, ebx
	or eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1296], eax
	mov eax, 27664
	and eax, ebx
	or eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1300], eax
	mov eax, 31980
	and eax, ebx
	or eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1304], eax
	mov eax, 8240
	and eax, ebx
	or eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1308], eax
	mov eax, 11901
	and eax, ebx
	or eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1312], eax
	mov eax, 24346
	and eax, ebx
	or eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1316], eax
	mov eax, 18070
	and eax, ebx
	or eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1320], eax
	mov eax, 59401
	and eax, ebx
	or eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1324], eax
	mov eax, ecx
	xor eax, 5
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 58437
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 3012
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 46212
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 8815
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 13096
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 51575
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 36918
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 41579
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 35597
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 48803
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 42323
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 47716
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 57271
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 10605
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 22934
	and eax, ebx
	or eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1144], eax
	mov eax, 14841
	and eax, ebx
	or eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1148], eax
	mov eax, 24542
	and eax, ebx
	or eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1152], eax
	mov eax, 31518
	and eax, ebx
	or eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1156], eax
	mov eax, 2233
	and eax, ebx
	or eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1160], eax
	mov eax, 29076
	and eax, ebx
	or eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1164], eax
	mov eax, 17617
	and eax, ebx
	or eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1168], eax
	mov eax, 14645
	and eax, ebx
	or eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1172], eax
	mov eax, 64083
	and eax, ebx
	or eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1176], eax
	mov eax, 36645
	and eax, ebx
	or eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1180], eax
	mov eax, 2944
	and eax, ebx
	or eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+1184], eax
	mov eax, 36904
	and eax, ebx
	or eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+1188], eax
	mov eax, 26189
	and eax, ebx
	or eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1192], eax
	mov eax, 6443
	and eax, ebx
	or eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1196], eax
	mov eax, 24187
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 10097
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 36296
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 34575
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 22347
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 35294
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 25670
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 52487
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 41534
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 26260
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 43266
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 59500
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 32677
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 54359
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 15572
	and eax, ebx
	or eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1272], eax
	mov eax, 28337
	and eax, ebx
	or eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1276], eax
	mov eax, 46737
	and eax, ebx
	or eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1280], eax
	mov eax, 34933
	and eax, ebx
	or eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1284], eax
	mov eax, 23574
	and eax, ebx
	or eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1288], eax
	mov eax, 27134
	and eax, ebx
	or eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1292], eax
	mov eax, 54123
	and eax, ebx
	or eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1296], eax
	mov eax, 17171
	and eax, ebx
	or eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1300], eax
	mov eax, 9275
	and eax, ebx
	or eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1304], eax
	mov eax, 27144
	and eax, ebx
	or eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1308], eax
	mov eax, 7977
	and eax, ebx
	or eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1312], eax
	mov eax, 60028
	and eax, ebx
	or eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1316], eax
	mov eax, 57034
	and eax, ebx
	or eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1320], eax
	mov eax, 9623
	and eax, ebx
	or eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1324], eax
	mov eax, ecx
	xor eax, 6
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 14474
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 32913
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 20731
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 53187
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 3153
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 49557
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 22543
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 6110
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 45833
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 24136
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 8677
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 37816
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 16696
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 16113
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 29228
	and eax, ebx
	or eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1144], eax
	mov eax, 9816
	and eax, ebx
	or eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1148], eax
	mov eax, 61459
	and eax, ebx
	or eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1152], eax
	mov eax, 46482
	and eax, ebx
	or eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1156], eax
	mov eax, 51139
	and eax, ebx
	or eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1160], eax
	mov eax, 31151
	and eax, ebx
	or eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1164], eax
	mov eax, 4290
	and eax, ebx
	or eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1168], eax
	mov eax, 7241
	and eax, ebx
	or eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1172], eax
	mov eax, 53399
	and eax, ebx
	or eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1176], eax
	mov eax, 1975
	and eax, ebx
	or eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1180], eax
	mov eax, 2610
	and eax, ebx
	or eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+1184], eax
	mov eax, 53398
	and eax, ebx
	or eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+1188], eax
	mov eax, 10171
	and eax, ebx
	or eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1192], eax
	mov eax, 19795
	and eax, ebx
	or eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1196], eax
	mov eax, 21635
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 34585
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 5667
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 45708
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 8045
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 52909
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 47073
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 53570
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 51834
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 8319
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 17816
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 48065
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 22159
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 11681
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 51806
	and eax, ebx
	or eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1272], eax
	mov eax, 211
	and eax, ebx
	or eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1276], eax
	mov eax, 56841
	and eax, ebx
	or eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1280], eax
	mov eax, 23685
	and eax, ebx
	or eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1284], eax
	mov eax, 10583
	and eax, ebx
	or eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1288], eax
	mov eax, 3207
	and eax, ebx
	or eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1292], eax
	mov eax, 45951
	and eax, ebx
	or eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1296], eax
	mov eax, 11479
	and eax, ebx
	or eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1300], eax
	mov eax, 19301
	and eax, ebx
	or eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1304], eax
	mov eax, 43914
	and eax, ebx
	or eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1308], eax
	mov eax, 24724
	and eax, ebx
	or eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1312], eax
	mov eax, 37738
	and eax, ebx
	or eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1316], eax
	mov eax, 30909
	and eax, ebx
	or eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1320], eax
	mov eax, 9490
	and eax, ebx
	or eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1324], eax
	mov eax, ecx
	xor eax, 7
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 48018
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 8789
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 33814
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 58350
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 1992
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 17406
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 31447
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 39189
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 36739
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 37216
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 38475
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 49634
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 24633
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 15360
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 65388
	and eax, ebx
	or eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1144], eax
	mov eax, 10092
	and eax, ebx
	or eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1148], eax
	mov eax, 48251
	and eax, ebx
	or eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1152], eax
	mov eax, 22091
	and eax, ebx
	or eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1156], eax
	mov eax, 52884
	and eax, ebx
	or eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1160], eax
	mov eax, 20060
	and eax, ebx
	or eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1164], eax
	mov eax, 41141
	and eax, ebx
	or eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1168], eax
	mov eax, 41217
	and eax, ebx
	or eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1172], eax
	mov eax, 13492
	and eax, ebx
	or eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1176], eax
	mov eax, 39906
	and eax, ebx
	or eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1180], eax
	mov eax, 38109
	and eax, ebx
	or eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+1184], eax
	mov eax, 14026
	and eax, ebx
	or eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+1188], eax
	mov eax, 40475
	and eax, ebx
	or eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1192], eax
	mov eax, 19260
	and eax, ebx
	or eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1196], eax
	mov eax, 34516
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 15165
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 62538
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 61831
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 43835
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 44678
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 5402
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 33102
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 56270
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 41689
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 53934
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 27564
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 55158
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 41298
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 32136
	and eax, ebx
	or eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1272], eax
	mov eax, 46565
	and eax, ebx
	or eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1276], eax
	mov eax, 925
	and eax, ebx
	or eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1280], eax
	mov eax, 9857
	and eax, ebx
	or eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1284], eax
	mov eax, 6423
	and eax, ebx
	or eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1288], eax
	mov eax, 18129
	and eax, ebx
	or eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1292], eax
	mov eax, 2025
	and eax, ebx
	or eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1296], eax
	mov eax, 63319
	and eax, ebx
	or eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1300], eax
	mov eax, 28836
	and eax, ebx
	or eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1304], eax
	mov eax, 23428
	and eax, ebx
	or eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1308], eax
	mov eax, 4640
	and eax, ebx
	or eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1312], eax
	mov eax, 21087
	and eax, ebx
	or eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1316], eax
	mov eax, 50896
	and eax, ebx
	or eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1320], eax
	mov eax, 40154
	and eax, ebx
	or eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1324], eax
	mov eax, ecx
	xor eax, 8
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 49344
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 13468
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 6279
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 22766
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 7056
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 59148
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 35784
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 37558
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 53445
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 11851
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 57545
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 45647
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 64862
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 29280
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 57302
	and eax, ebx
	or eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1144], eax
	mov eax, 15162
	and eax, ebx
	or eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1148], eax
	mov eax, 22918
	and eax, ebx
	or eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1152], eax
	mov eax, 18442
	and eax, ebx
	or eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1156], eax
	mov eax, 14413
	and eax, ebx
	or eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1160], eax
	mov eax, 62394
	and eax, ebx
	or eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1164], eax
	mov eax, 42806
	and eax, ebx
	or eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1168], eax
	mov eax, 15438
	and eax, ebx
	or eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1172], eax
	mov eax, 55517
	and eax, ebx
	or eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1176], eax
	mov eax, 23977
	and eax, ebx
	or eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1180], eax
	mov eax, 64572
	and eax, ebx
	or eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+1184], eax
	mov eax, 39031
	and eax, ebx
	or eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+1188], eax
	mov eax, 22954
	and eax, ebx
	or eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1192], eax
	mov eax, 35673
	and eax, ebx
	or eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1196], eax
	mov eax, 30547
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 57400
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 11148
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 51855
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 38785
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 22366
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 17891
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 59504
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 41248
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 33060
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 26522
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 25483
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 29711
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 18190
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 64625
	and eax, ebx
	or eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1272], eax
	mov eax, 30890
	and eax, ebx
	or eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1276], eax
	mov eax, 43925
	and eax, ebx
	or eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1280], eax
	mov eax, 47631
	and eax, ebx
	or eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1284], eax
	mov eax, 34949
	and eax, ebx
	or eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1288], eax
	mov eax, 44387
	and eax, ebx
	or eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1292], eax
	mov eax, 14233
	and eax, ebx
	or eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1296], eax
	mov eax, 61141
	and eax, ebx
	or eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1300], eax
	mov eax, 15226
	and eax, ebx
	or eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1304], eax
	mov eax, 31128
	and eax, ebx
	or eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1308], eax
	mov eax, 18636
	and eax, ebx
	or eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1312], eax
	mov eax, 49650
	and eax, ebx
	or eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1316], eax
	mov eax, 17750
	and eax, ebx
	or eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1320], eax
	mov eax, 8739
	and eax, ebx
	or eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1324], eax
	mov eax, ecx
	xor eax, 9
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 44824
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 64447
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 28821
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 54856
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 17629
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 46873
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 62983
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 25224
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 54132
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 14640
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 28427
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 61841
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 59726
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 34998
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 20703
	and eax, ebx
	or eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1144], eax
	mov eax, 36092
	and eax, ebx
	or eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1148], eax
	mov eax, 21066
	and eax, ebx
	or eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1152], eax
	mov eax, 35372
	and eax, ebx
	or eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1156], eax
	mov eax, 13606
	and eax, ebx
	or eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1160], eax
	mov eax, 3173
	and eax, ebx
	or eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1164], eax
	mov eax, 30108
	and eax, ebx
	or eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1168], eax
	mov eax, 1824
	and eax, ebx
	or eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1172], eax
	mov eax, 27263
	and eax, ebx
	or eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1176], eax
	mov eax, 27685
	and eax, ebx
	or eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1180], eax
	mov eax, 64311
	and eax, ebx
	or eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+1184], eax
	mov eax, 26136
	and eax, ebx
	or eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+1188], eax
	mov eax, 62858
	and eax, ebx
	or eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1192], eax
	mov eax, 18366
	and eax, ebx
	or eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1196], eax
	mov eax, 64448
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 39591
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 20708
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 62791
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 57928
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 24828
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 22008
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 17688
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 56308
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 53746
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 13071
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 30002
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 60895
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 51316
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 53581
	and eax, ebx
	or eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1272], eax
	mov eax, 13323
	and eax, ebx
	or eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1276], eax
	mov eax, 50758
	and eax, ebx
	or eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1280], eax
	mov eax, 1550
	and eax, ebx
	or eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1284], eax
	mov eax, 17846
	and eax, ebx
	or eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1288], eax
	mov eax, 18189
	and eax, ebx
	or eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1292], eax
	mov eax, 43159
	and eax, ebx
	or eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1296], eax
	mov eax, 55564
	and eax, ebx
	or eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1300], eax
	mov eax, 26133
	and eax, ebx
	or eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1304], eax
	mov eax, 21257
	and eax, ebx
	or eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1308], eax
	mov eax, 10965
	and eax, ebx
	or eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1312], eax
	mov eax, 24135
	and eax, ebx
	or eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1316], eax
	mov eax, 34099
	and eax, ebx
	or eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1320], eax
	mov eax, 18772
	and eax, ebx
	or eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1324], eax
	mov eax, ecx
	xor eax, 10
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 55056
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 476
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 62865
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 64018
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 29884
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 8631
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 27876
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 64910
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 9494
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 57901
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 35956
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 42326
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 58065
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 10042
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 37371
	and eax, ebx
	or eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1144], eax
	mov eax, 6366
	and eax, ebx
	or eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1148], eax
	mov eax, 37553
	and eax, ebx
	or eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1152], eax
	mov eax, 24245
	and eax, ebx
	or eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1156], eax
	mov eax, 17019
	and eax, ebx
	or eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1160], eax
	mov eax, 3501
	and eax, ebx
	or eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1164], eax
	mov eax, 10723
	and eax, ebx
	or eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1168], eax
	mov eax, 40889
	and eax, ebx
	or eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1172], eax
	mov eax, 55906
	and eax, ebx
	or eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1176], eax
	mov eax, 33465
	and eax, ebx
	or eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1180], eax
	mov eax, 46547
	and eax, ebx
	or eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+1184], eax
	mov eax, 57262
	and eax, ebx
	or eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+1188], eax
	mov eax, 11449
	and eax, ebx
	or eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1192], eax
	mov eax, 28136
	and eax, ebx
	or eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1196], eax
	mov eax, 33371
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 22660
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 46164
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 41973
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 2477
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 29037
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 55786
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 29009
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 23028
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 48620
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 26463
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 44414
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 8104
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 54764
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 59489
	and eax, ebx
	or eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1272], eax
	mov eax, 15544
	and eax, ebx
	or eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1276], eax
	mov eax, 28203
	and eax, ebx
	or eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1280], eax
	mov eax, 22297
	and eax, ebx
	or eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1284], eax
	mov eax, 2933
	and eax, ebx
	or eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1288], eax
	mov eax, 41790
	and eax, ebx
	or eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1292], eax
	mov eax, 10109
	and eax, ebx
	or eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1296], eax
	mov eax, 18220
	and eax, ebx
	or eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1300], eax
	mov eax, 63852
	and eax, ebx
	or eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1304], eax
	mov eax, 35274
	and eax, ebx
	or eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1308], eax
	mov eax, 20957
	and eax, ebx
	or eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1312], eax
	mov eax, 46268
	and eax, ebx
	or eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1316], eax
	mov eax, 32598
	and eax, ebx
	or eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1320], eax
	mov eax, 55397
	and eax, ebx
	or eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1324], eax
	mov eax, ecx
	xor eax, 11
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 29145
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 22174
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 20126
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 33045
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 41530
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 28917
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 15967
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 35057
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 8975
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 35036
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 17295
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 51445
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 58767
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 10149
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 37754
	and eax, ebx
	or eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1144], eax
	mov eax, 1598
	and eax, ebx
	or eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1148], eax
	mov eax, 13922
	and eax, ebx
	or eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1152], eax
	mov eax, 57730
	and eax, ebx
	or eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1156], eax
	mov eax, 2268
	and eax, ebx
	or eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1160], eax
	mov eax, 8595
	and eax, ebx
	or eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1164], eax
	mov eax, 45316
	and eax, ebx
	or eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1168], eax
	mov eax, 29143
	and eax, ebx
	or eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1172], eax
	mov eax, 1865
	and eax, ebx
	or eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1176], eax
	mov eax, 1724
	and eax, ebx
	or eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1180], eax
	mov eax, 60381
	and eax, ebx
	or eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+1184], eax
	mov eax, 13261
	and eax, ebx
	or eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+1188], eax
	mov eax, 5470
	and eax, ebx
	or eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1192], eax
	mov eax, 14467
	and eax, ebx
	or eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1196], eax
	mov eax, 22273
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 5398
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 50503
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 60743
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 42674
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 36239
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 43469
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 38296
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 5241
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 20474
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 25150
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 41359
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 40386
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 42659
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 39353
	and eax, ebx
	or eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1272], eax
	mov eax, 22562
	and eax, ebx
	or eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1276], eax
	mov eax, 13780
	and eax, ebx
	or eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1280], eax
	mov eax, 30841
	and eax, ebx
	or eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1284], eax
	mov eax, 23961
	and eax, ebx
	or eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1288], eax
	mov eax, 39646
	and eax, ebx
	or eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1292], eax
	mov eax, 58620
	and eax, ebx
	or eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1296], eax
	mov eax, 13993
	and eax, ebx
	or eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1300], eax
	mov eax, 58104
	and eax, ebx
	or eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1304], eax
	mov eax, 40034
	and eax, ebx
	or eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1308], eax
	mov eax, 59003
	and eax, ebx
	or eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1312], eax
	mov eax, 4027
	and eax, ebx
	or eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1316], eax
	mov eax, 37654
	and eax, ebx
	or eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1320], eax
	mov eax, 60288
	and eax, ebx
	or eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1324], eax
	mov eax, ecx
	xor eax, 12
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 35446
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 34650
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 15232
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 64124
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 22814
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 18781
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 45868
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 11037
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 16506
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 55801
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 54656
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 38808
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 10503
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 19146
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 36036
	and eax, ebx
	or eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1144], eax
	mov eax, 64984
	and eax, ebx
	or eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1148], eax
	mov eax, 55135
	and eax, ebx
	or eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1152], eax
	mov eax, 36129
	and eax, ebx
	or eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1156], eax
	mov eax, 64535
	and eax, ebx
	or eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1160], eax
	mov eax, 62588
	and eax, ebx
	or eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1164], eax
	mov eax, 18458
	and eax, ebx
	or eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1168], eax
	mov eax, 23999
	and eax, ebx
	or eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1172], eax
	mov eax, 58963
	and eax, ebx
	or eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1176], eax
	mov eax, 909
	and eax, ebx
	or eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1180], eax
	mov eax, 52599
	and eax, ebx
	or eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+1184], eax
	mov eax, 36644
	and eax, ebx
	or eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+1188], eax
	mov eax, 13044
	and eax, ebx
	or eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1192], eax
	mov eax, 2917
	and eax, ebx
	or eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1196], eax
	mov eax, 48481
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 17004
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 26804
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 22350
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 36122
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 35062
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 33971
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 27649
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 40428
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 25561
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 64579
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 57881
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 38538
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 2346
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 56816
	and eax, ebx
	or eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1272], eax
	mov eax, 62826
	and eax, ebx
	or eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1276], eax
	mov eax, 39250
	and eax, ebx
	or eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1280], eax
	mov eax, 18335
	and eax, ebx
	or eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1284], eax
	mov eax, 65413
	and eax, ebx
	or eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1288], eax
	mov eax, 27564
	and eax, ebx
	or eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1292], eax
	mov eax, 47145
	and eax, ebx
	or eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1296], eax
	mov eax, 3895
	and eax, ebx
	or eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1300], eax
	mov eax, 58026
	and eax, ebx
	or eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1304], eax
	mov eax, 25552
	and eax, ebx
	or eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1308], eax
	mov eax, 16561
	and eax, ebx
	or eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1312], eax
	mov eax, 60833
	and eax, ebx
	or eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1316], eax
	mov eax, 11130
	and eax, ebx
	or eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1320], eax
	mov eax, 47938
	and eax, ebx
	or eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1324], eax
	mov eax, ecx
	xor eax, 13
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 23257
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 32518
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 45524
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 43007
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 35532
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 54238
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 51289
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 38695
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 34940
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 21582
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 6520
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 17805
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 22343
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 36059
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 10596
	and eax, ebx
	or eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1144], eax
	mov eax, 15560
	and eax, ebx
	or eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1148], eax
	mov eax, 49521
	and eax, ebx
	or eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1152], eax
	mov eax, 64800
	and eax, ebx
	or eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1156], eax
	mov eax, 43252
	and eax, ebx
	or eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1160], eax
	mov eax, 17245
	and eax, ebx
	or eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1164], eax
	mov eax, 8895
	and eax, ebx
	or eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1168], eax
	mov eax, 38973
	and eax, ebx
	or eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1172], eax
	mov eax, 17268
	and eax, ebx
	or eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1176], eax
	mov eax, 50727
	and eax, ebx
	or eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1180], eax
	mov eax, 2029
	and eax, ebx
	or eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+1184], eax
	mov eax, 29447
	and eax, ebx
	or eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+1188], eax
	mov eax, 22002
	and eax, ebx
	or eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1192], eax
	mov eax, 64608
	and eax, ebx
	or eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1196], eax
	mov eax, 27388
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 9927
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 14431
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 50543
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 23821
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 63851
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 55900
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 38678
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 24778
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 8764
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 50310
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 18396
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 27658
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 8150
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 15978
	and eax, ebx
	or eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1272], eax
	mov eax, 65109
	and eax, ebx
	or eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1276], eax
	mov eax, 50507
	and eax, ebx
	or eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1280], eax
	mov eax, 38716
	and eax, ebx
	or eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1284], eax
	mov eax, 39489
	and eax, ebx
	or eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1288], eax
	mov eax, 61360
	and eax, ebx
	or eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1292], eax
	mov eax, 34143
	and eax, ebx
	or eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1296], eax
	mov eax, 24258
	and eax, ebx
	or eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1300], eax
	mov eax, 29104
	and eax, ebx
	or eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1304], eax
	mov eax, 8962
	and eax, ebx
	or eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1308], eax
	mov eax, 53099
	and eax, ebx
	or eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1312], eax
	mov eax, 43580
	and eax, ebx
	or eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1316], eax
	mov eax, 46182
	and eax, ebx
	or eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1320], eax
	mov eax, 15103
	and eax, ebx
	or eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1324], eax
	mov eax, ecx
	xor eax, 14
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 33919
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 7328
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 54680
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 23208
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 54466
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 57028
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 43660
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 57984
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 9318
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 46924
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 39357
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 7432
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 14532
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 11672
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 51845
	and eax, ebx
	or eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1144], eax
	mov eax, 43478
	and eax, ebx
	or eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1148], eax
	mov eax, 12600
	and eax, ebx
	or eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1152], eax
	mov eax, 52407
	and eax, ebx
	or eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1156], eax
	mov eax, 38984
	and eax, ebx
	or eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1160], eax
	mov eax, 43028
	and eax, ebx
	or eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1164], eax
	mov eax, 44834
	and eax, ebx
	or eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1168], eax
	mov eax, 64442
	and eax, ebx
	or eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1172], eax
	mov eax, 46461
	and eax, ebx
	or eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1176], eax
	mov eax, 61337
	and eax, ebx
	or eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1180], eax
	mov eax, 46628
	and eax, ebx
	or eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+1184], eax
	mov eax, 36740
	and eax, ebx
	or eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+1188], eax
	mov eax, 62474
	and eax, ebx
	or eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1192], eax
	mov eax, 57073
	and eax, ebx
	or eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1196], eax
	mov eax, 8050
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 50755
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 31932
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 29488
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 30703
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 47071
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 26848
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 47004
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 43437
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 64665
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 19429
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 46037
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 48153
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 1878
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 35023
	and eax, ebx
	or eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1272], eax
	mov eax, 21150
	and eax, ebx
	or eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1276], eax
	mov eax, 45877
	and eax, ebx
	or eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1280], eax
	mov eax, 4037
	and eax, ebx
	or eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1284], eax
	mov eax, 36312
	and eax, ebx
	or eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1288], eax
	mov eax, 60797
	and eax, ebx
	or eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1292], eax
	mov eax, 10316
	and eax, ebx
	or eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1296], eax
	mov eax, 34429
	and eax, ebx
	or eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1300], eax
	mov eax, 55592
	and eax, ebx
	or eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1304], eax
	mov eax, 10979
	and eax, ebx
	or eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1308], eax
	mov eax, 53779
	and eax, ebx
	or eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1312], eax
	mov eax, 57120
	and eax, ebx
	or eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1316], eax
	mov eax, 32736
	and eax, ebx
	or eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1320], eax
	mov eax, 22458
	and eax, ebx
	or eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1324], eax
	mov eax, ecx
	xor eax, 15
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 35654
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 33295
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 52249
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 36550
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 31247
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 41842
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 57428
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 22554
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 23461
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 33020
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 34774
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 8628
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 26816
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 46970
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 14340
	and eax, ebx
	or eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+1144], eax
	mov eax, 44966
	and eax, ebx
	or eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+1148], eax
	mov eax, 36004
	and eax, ebx
	or eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+1152], eax
	mov eax, 12366
	and eax, ebx
	or eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+1156], eax
	mov eax, 42783
	and eax, ebx
	or eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+1160], eax
	mov eax, 61552
	and eax, ebx
	or eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+1164], eax
	mov eax, 59040
	and eax, ebx
	or eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+1168], eax
	mov eax, 61735
	and eax, ebx
	or eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+1172], eax
	mov eax, 33914
	and eax, ebx
	or eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+1176], eax
	mov eax, 40468
	and eax, ebx
	or eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+1180], eax
	mov eax, 21491
	and eax, ebx
	or eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+1184], eax
	mov eax, 41915
	and eax, ebx
	or eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+1188], eax
	mov eax, 58044
	and eax, ebx
	or eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1192], eax
	mov eax, 28318
	and eax, ebx
	or eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1196], eax
	mov eax, 8194
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 24629
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 5133
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 52101
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 32300
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 2622
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 43597
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 23322
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 46167
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 49795
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 54621
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 23156
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 46461
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 49337
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 59234
	and eax, ebx
	or eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1272], eax
	mov eax, 2413
	and eax, ebx
	or eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1276], eax
	mov eax, 13144
	and eax, ebx
	or eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1280], eax
	mov eax, 18996
	and eax, ebx
	or eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1284], eax
	mov eax, 36358
	and eax, ebx
	or eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1288], eax
	mov eax, 40745
	and eax, ebx
	or eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1292], eax
	mov eax, 56651
	and eax, ebx
	or eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1296], eax
	mov eax, 37509
	and eax, ebx
	or eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1300], eax
	mov eax, 26408
	and eax, ebx
	or eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1304], eax
	mov eax, 12280
	and eax, ebx
	or eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1308], eax
	mov eax, 47057
	and eax, ebx
	or eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1312], eax
	mov eax, 40403
	and eax, ebx
	or eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1316], eax
	mov eax, 63601
	and eax, ebx
	or eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1320], eax
	mov eax, 44485
	and eax, ebx
	or eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1324], eax
	mov eax, 1600
	mov ecx, 320
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
	mov eax, 1728
	mov ecx, 1600
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 64
	mov edx, 1088
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 192
	mov edx, 1216
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 1472
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
	mov eax, 2240
	mov ecx, 1728
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 1728
	mov edx, 2112
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 64
	mov edx, 192
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 1088
	mov edx, 1216
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
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
	mov eax, 2624
	mov ecx, 1600
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
	mov eax, 2496
	mov ecx, 2496
	mov edx, 1856
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 2496
	mov edx, 1984
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
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
	mov eax, 2624
	mov ecx, 1600
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
	mov eax, 2496
	mov ecx, 1984
	mov edx, 1856
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
	mov eax, 704
	mov ecx, 2240
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
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+516]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+520]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+524]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+784]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+788]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+792]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+796]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+800]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+804]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+808]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+812]
	mov DWORD PTR [edi+428], eax
	cmp esi, 0
	jne 22b
	mov eax, 320
	mov ecx, 64
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 192
	mov ecx, 192
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
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
23:
	mov eax, 1856
	mov ecx, 1856
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 23b
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
24:
	mov eax, 1984
	mov ecx, 1984
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 24b
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
25:
	mov eax, 2112
	mov ecx, 2112
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 25b
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
26:
	mov eax, 2240
	mov ecx, 2240
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 26b
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
27:
	mov eax, 2368
	mov ecx, 2368
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 27b
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
28:
	mov eax, 2496
	mov ecx, 2496
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 28b
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
29:
	mov eax, 2624
	mov ecx, 2624
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
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
	mov esi, 64
210:
	mov eax, 2624
	mov ecx, 2624
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 210b
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
211:
	mov eax, 2624
	mov ecx, 2624
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 211b
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
212:
	mov eax, 2624
	mov ecx, 2624
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 212b
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
213:
	mov eax, 2624
	mov ecx, 2624
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 213b
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
214:
	mov eax, 2624
	mov ecx, 2624
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 214b
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
215:
	mov eax, 2752
	mov ecx, 2752
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 215b
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
216:
	mov eax, 2752
	mov ecx, 2752
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 216b
	mov esi, 2
217:
	mov eax, 2624
	mov ecx, 2624
	push ecx
	push eax
	push edi
	call {vg_gf448_r16_sqr}
	pop eax
	pop eax
	pop eax
	sub esi, 1
	jne 217b
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
