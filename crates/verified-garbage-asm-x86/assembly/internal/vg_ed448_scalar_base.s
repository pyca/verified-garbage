// The functions of `src/internal/vg_ed448_scalar_base.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_scalar_base:
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
	mov eax, -955465634
	mov DWORD PTR [ebp+1024], eax
	mov eax, 640067627
	mov DWORD PTR [ebp+1028], eax
	mov eax, -1962896498
	mov DWORD PTR [ebp+1032], eax
	mov eax, 1127973089
	mov DWORD PTR [ebp+1036], eax
	mov eax, 716596497
	mov DWORD PTR [ebp+1040], eax
	mov eax, 313400055
	mov DWORD PTR [ebp+1044], eax
	mov eax, -1546410908
	mov DWORD PTR [ebp+1048], eax
	mov eax, -361897180
	mov DWORD PTR [ebp+1052], eax
	mov eax, 1192171367
	mov DWORD PTR [ebp+1056], eax
	mov eax, -1642830480
	mov DWORD PTR [ebp+1060], eax
	mov eax, 582956762
	mov DWORD PTR [ebp+1064], eax
	mov eax, 572331430
	mov DWORD PTR [ebp+1068], eax
	mov eax, 1810697709
	mov DWORD PTR [ebp+1072], eax
	mov eax, 1327067334
	mov DWORD PTR [ebp+1076], eax
	mov eax, -231671276
	mov DWORD PTR [ebp+1152], eax
	mov eax, -1744275109
	mov DWORD PTR [ebp+1156], eax
	mov eax, 1322764461
	mov DWORD PTR [ebp+1160], eax
	mov eax, -37940436
	mov DWORD PTR [ebp+1164], eax
	mov eax, -428066364
	mov DWORD PTR [ebp+1168], eax
	mov eax, 986971932
	mov DWORD PTR [ebp+1172], eax
	mov eax, 94421719
	mov DWORD PTR [ebp+1176], eax
	mov eax, -2022138850
	mov DWORD PTR [ebp+1180], eax
	mov eax, 1822660672
	mov DWORD PTR [ebp+1184], eax
	mov eax, 1273656179
	mov DWORD PTR [ebp+1188], eax
	mov eax, 1456064354
	mov DWORD PTR [ebp+1192], eax
	mov eax, -2005524425
	mov DWORD PTR [ebp+1196], eax
	mov eax, 1857469476
	mov DWORD PTR [ebp+1200], eax
	mov eax, 1765754481
	mov DWORD PTR [ebp+1204], eax
	mov eax, 1
	mov DWORD PTR [ebp+1280], eax
	mov eax, -39082
	mov DWORD PTR [ebp+1408], eax
	mov eax, -1
	mov DWORD PTR [ebp+1412], eax
	mov eax, -1
	mov DWORD PTR [ebp+1416], eax
	mov eax, -1
	mov DWORD PTR [ebp+1420], eax
	mov eax, -1
	mov DWORD PTR [ebp+1424], eax
	mov eax, -1
	mov DWORD PTR [ebp+1428], eax
	mov eax, -1
	mov DWORD PTR [ebp+1432], eax
	mov eax, -2
	mov DWORD PTR [ebp+1436], eax
	mov eax, -1
	mov DWORD PTR [ebp+1440], eax
	mov eax, -1
	mov DWORD PTR [ebp+1444], eax
	mov eax, -1
	mov DWORD PTR [ebp+1448], eax
	mov eax, -1
	mov DWORD PTR [ebp+1452], eax
	mov eax, -1
	mov DWORD PTR [ebp+1456], eax
	mov eax, -1
	mov DWORD PTR [ebp+1460], eax
	mov esi, DWORD PTR [esp+8]
	mov ebp, edi
	mov ecx, 57
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
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1600
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 64
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 192
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 320
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_add}
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
	call {vg_gf448_r32_sub}
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
	call {vg_gf448_r32_sub}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_sub}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_mul}
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
	mov eax, ecx
	xor eax, 1
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, -955465634
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 640067627
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, -1962896498
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 1127973089
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 716596497
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 313400055
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, -1546410908
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, -361897180
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 1192171367
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, -1642830480
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 582956762
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 572331430
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 1810697709
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 1327067334
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, -231671276
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, -1744275109
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 1322764461
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, -37940436
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, -428066364
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 986971932
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 94421719
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, -2022138850
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 1822660672
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 1273656179
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 1456064354
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, -2005524425
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 1857469476
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 1765754481
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 2
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, -1930993064
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 1973655672
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, -797666119
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, -538824655
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 1835343939
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 1140976714
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, -619019109
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, -1125598260
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, -1627906373
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, -730763522
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 1590465405
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 422907640
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 338115484
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 638423842
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, -411307613
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, -1222803935
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 1754944590
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, -313517667
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, -1517020852
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, -1599165795
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 1906707432
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, -496157871
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 672676362
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 1990778775
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 108284401
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 1131864867
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 626269300
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, -1295310418
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 3
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, -1330180329
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, -1602597678
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 817486766
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 303368350
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, -1820420224
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, -552800454
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, -988233909
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, -485952643
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, -1106536010
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 2143574590
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 211875291
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 1034342241
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, -1196646638
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, -819338741
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, -1207053069
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 663731394
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, -124330057
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, -1790747940
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 2092608113
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, -1433365581
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, -2000805440
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, -815709065
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, -310429642
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, -917605155
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, -910195030
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, -1167495528
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, -1275381990
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 705701861
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 4
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 1972287072
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 1274505576
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, -97831446
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 270235610
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 1300500130
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, -1824324251
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, -1577643983
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, -855230016
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, -537338776
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 196435967
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, -1207565691
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 1615528709
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 1988192774
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 70870931
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 325218965
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, -1612481671
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 121079258
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 1881169831
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 1461608160
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, -1574365893
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, -51911553
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, -381237521
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, -981663065
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 896926797
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 1813023419
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 540048620
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 1595551357
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, -402045290
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 5
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 197452869
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 577746052
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, -914935000
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, -1570009034
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, -1096578291
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, -1167809197
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 695066551
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 972642710
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 2065588190
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 1905526969
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 959792337
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, -1893336493
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, -1876423808
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 422274637
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 661741179
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, -2029023800
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, -1981917365
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, -855153594
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 1721016894
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, -395532030
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, -732463195
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 1857109204
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, -2005551471
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 1778277398
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 1125372779
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 1778918459
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, -360964311
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 630709962
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 6
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, -2137966454
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, -809283333
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, -1047196591
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 400447503
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 1581822729
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, -1816649243
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 1055998264
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 643330604
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, -1248661485
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 2041563075
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 474550466
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 129486999
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, -795473358
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 1297295291
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, -2028383101
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, -1299442141
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, -827515027
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, -784156703
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 545245818
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, -1144961640
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 765548175
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 13879902
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 1552277001
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 210184535
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 752333695
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, -1417000091
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, -1821745004
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 621967549
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 7
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 576043922
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, -470907882
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 1140721608
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, -1726645545
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, -1855942781
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, -1042114997
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 1006657593
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 661454700
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 1447804027
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 1314705044
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, -1593728843
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, -1679674188
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 919246045
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 1262263835
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 993887956
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, -242748342
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, -1366906053
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, -2125589222
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, -1562780722
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 1806488238
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, -1588406410
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, -1243251320
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 645989277
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 1188108567
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, -145291287
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 1535406244
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 1381962272
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, -1663383856
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 8
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 882688192
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 1491998855
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, -418636912
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, -1833530424
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 776720581
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, -1303387959
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 1918958942
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 993714134
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 1208637830
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, -205899699
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 1011787574
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 1571412189
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, -1736967108
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, -1957078614
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, -533170349
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, -896586868
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 1465816961
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, -395295261
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, -2128305888
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 1670080410
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 1192129551
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 2024471665
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, -1173378155
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, -1385985915
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, -288016487
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 2040019834
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, -1041086260
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 572736854
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 9
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, -71323880
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, -699895659
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, -1223080739
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 1653143047
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 959501172
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, -242127093
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, -2001278642
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, -1929621281
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, -1976806838
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 207959334
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 119567772
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 1814391423
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 1712913207
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 1203697034
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, -1700267072
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, -179875612
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 1627185736
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 1159222776
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, -772613132
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 1966224143
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, -931861025
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 873189709
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 101631558
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 1192052150
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, -653481833
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 1393124885
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 1581722325
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 1230275891
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 10
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 31250192
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, -99420783
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 565671100
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, -40997660
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, -500357866
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, -1521054604
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 658170577
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 417239547
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 1588957873
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 229458555
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, -1615255069
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, -2101749150
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, -542198317
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 1843932345
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 1485079131
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, -1544178604
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 1902971309
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 1901189610
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, -1108583948
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, -1384224929
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, -705945688
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 1018751073
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 1461284395
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, -1556214923
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 1194076029
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, -1983186580
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, -1262726691
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, -664436906
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 11
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 1453224409
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, -2129310050
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 1895146042
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, -1997455777
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, -1998839025
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, -923450481
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 665183631
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 104764282
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, -511560094
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 563284188
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 1909960964
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 112985929
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 869133277
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 948114782
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 353785601
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, -314063545
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, -1919965518
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, -1785157171
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 1341789305
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, -1584438722
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, -1499226686
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 1478662585
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 2021209556
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, -1696703079
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 917103868
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, -1671240968
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, 263972475
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, -343895274
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 12
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, -2024109450
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, -92521600
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, 1230854430
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 723366700
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, -637976454
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, -1751591552
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 1254762759
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, -36139836
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, -1927162017
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, -193135593
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, 1572816922
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, 59631187
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, -1893413513
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 191181556
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 1114422625
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 1464756404
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, -1997107942
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 1812038835
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 1675206124
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, -501613501
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 153785994
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, -177545744
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 1201641810
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, 1806499717
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 255309865
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 1674633898
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, -308199247
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, -1153291398
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 13
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 2131122905
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, -1476415020
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, -740390196
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, -1759000487
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, 1414432892
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 1166875000
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, -1931782329
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, 1019750756
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, -48184975
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, 1130211572
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, -1740823873
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, -970505356
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, 1929840621
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, -60795406
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 650603260
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, -982566817
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, -110404339
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, -1760109988
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, 574382282
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 1205650566
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 534146058
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, -27967894
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, -1757625013
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, -273638847
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, 1589806431
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 587362736
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, -1438855317
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 989836390
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 14
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, 480281727
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, 1521014168
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, -557525822
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, -494884212
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, -1219746714
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 487102909
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, 764950724
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, -1445541243
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, -860409544
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, -1475045304
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, -71651550
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, -275139203
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, -1887128028
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, -554568694
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, -968679566
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, 1932557500
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, -1210091537
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, -1214486304
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, -57038419
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, -1277867035
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, 123124761
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 1386121423
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 264614709
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, -310538792
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, -2038618036
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 719575336
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, -551497197
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, 1471840224
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 15
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, -2112910522
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, -1899574247
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, -1552778737
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, 1478156372
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, -2130945115
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, 565479382
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, -1216714560
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, -1348061180
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, 810454180
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, -261052641
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, -249043296
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, -1642822534
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, -1548004365
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, 1855906492
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, 1614094338
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, -880471027
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, 171867692
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, 1528474189
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, -1031556009
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, 1517606237
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, -1061571203
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, 158197602
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, 1244935000
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, -1624666618
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, -1836720821
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, 804808488
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, -1647069231
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, -1379534735
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 1600
	mov ecx, 320
	mov edx, 1344
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 1600
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_sub}
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
	call {vg_gf448_r32_add}
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
	call {vg_gf448_r32_add}
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
	call {vg_gf448_r32_add}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_sub}
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
	call {vg_gf448_r32_sub}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_sub}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_mul}
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
	cmp esi, 0
	jne 22b
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
	mov esi, 1
23:
	mov eax, 1856
	mov ecx, 1856
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_mul}
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
	mov esi, 2
24:
	mov eax, 1984
	mov ecx, 1984
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_mul}
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
	mov esi, 4
25:
	mov eax, 2112
	mov ecx, 2112
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_mul}
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
	mov esi, 8
26:
	mov eax, 2240
	mov ecx, 2240
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_mul}
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
	mov esi, 16
27:
	mov eax, 2368
	mov ecx, 2368
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_mul}
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
	mov esi, 32
28:
	mov eax, 2496
	mov ecx, 2496
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_mul}
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
	mov esi, 64
29:
	mov eax, 2624
	mov ecx, 2624
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_mul}
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
	mov esi, 1
215:
	mov eax, 2752
	mov ecx, 2752
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_sqr}
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
	call {vg_gf448_r32_mul}
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
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 192
	mov edx, 2752
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 192
	mov ecx, 64
	mov edx, 2752
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+192]
	adc eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	adc eax, 0
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	adc eax, 0
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	adc eax, 0
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	adc eax, 0
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	adc eax, 0
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	adc eax, 0
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	adc eax, 1
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	adc eax, 0
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	adc eax, 0
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	adc eax, 0
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	adc eax, 0
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	adc eax, 0
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	adc eax, 0
	mov DWORD PTR [edi+3892], eax
	sbb ecx, ecx
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
	mov esi, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+192]
	and eax, 1
	ror eax, 25
	mov BYTE PTR [esi+56], al
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
	xor ecx, ecx
	mov eax, DWORD PTR [edi+192]
	adc eax, 1
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+196]
	adc eax, 0
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+200]
	adc eax, 0
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+204]
	adc eax, 0
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+208]
	adc eax, 0
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+212]
	adc eax, 0
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+216]
	adc eax, 0
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+220]
	adc eax, 1
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+224]
	adc eax, 0
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+228]
	adc eax, 0
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+232]
	adc eax, 0
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+236]
	adc eax, 0
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+240]
	adc eax, 0
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+244]
	adc eax, 0
	mov DWORD PTR [edi+3892], eax
	sbb ecx, ecx
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
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [esi+52], eax
	mov eax, edi
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov ebp, DWORD PTR [eax+12]
	mov edi, DWORD PTR [eax+8]
	ret
	.p2align 6
