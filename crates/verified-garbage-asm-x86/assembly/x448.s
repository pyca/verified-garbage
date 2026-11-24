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
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-40]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	lea esp, [esp+40]
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
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
	mov eax, -801595463
	mov DWORD PTR [ebp], eax
	mov eax, -1558882940
	mov DWORD PTR [ebp+4], eax
	mov eax, 2140827528
	mov DWORD PTR [ebp+8], eax
	mov eax, -1039555887
	mov DWORD PTR [ebp+12], eax
	mov eax, -517291579
	mov DWORD PTR [ebp+16], eax
	mov eax, -1852100540
	mov DWORD PTR [ebp+20], eax
	mov eax, 1740859374
	mov DWORD PTR [ebp+24], eax
	mov eax, -2141304250
	mov DWORD PTR [ebp+28], eax
	mov eax, 1247229711
	mov DWORD PTR [ebp+32], eax
	mov eax, 2118320456
	mov DWORD PTR [ebp+36], eax
	mov eax, 328286178
	mov DWORD PTR [ebp+40], eax
	mov eax, 445110887
	mov DWORD PTR [ebp+44], eax
	mov eax, 2054594582
	mov DWORD PTR [ebp+48], eax
	mov eax, -877350605
	mov DWORD PTR [ebp+52], eax
	mov eax, -930584828
	mov DWORD PTR [ebp+128], eax
	mov eax, -238960028
	mov DWORD PTR [ebp+132], eax
	mov eax, -983310457
	mov DWORD PTR [ebp+136], eax
	mov eax, 1099921762
	mov DWORD PTR [ebp+140], eax
	mov eax, -1163750934
	mov DWORD PTR [ebp+144], eax
	mov eax, -702716183
	mov DWORD PTR [ebp+148], eax
	mov eax, -1848981984
	mov DWORD PTR [ebp+152], eax
	mov eax, -14370353
	mov DWORD PTR [ebp+156], eax
	mov eax, 650815121
	mov DWORD PTR [ebp+160], eax
	mov eax, -927176243
	mov DWORD PTR [ebp+164], eax
	mov eax, -976292479
	mov DWORD PTR [ebp+168], eax
	mov eax, 125794213
	mov DWORD PTR [ebp+172], eax
	mov eax, -463403115
	mov DWORD PTR [ebp+176], eax
	mov eax, -863109553
	mov DWORD PTR [ebp+180], eax
	mov eax, 1
	mov DWORD PTR [ebp+256], eax
	mov eax, -801595463
	mov DWORD PTR [ebp+384], eax
	mov eax, -1558882940
	mov DWORD PTR [ebp+388], eax
	mov eax, 2140827528
	mov DWORD PTR [ebp+392], eax
	mov eax, -1039555887
	mov DWORD PTR [ebp+396], eax
	mov eax, -517291579
	mov DWORD PTR [ebp+400], eax
	mov eax, -1852100540
	mov DWORD PTR [ebp+404], eax
	mov eax, 1740859374
	mov DWORD PTR [ebp+408], eax
	mov eax, -2141304250
	mov DWORD PTR [ebp+412], eax
	mov eax, 1247229711
	mov DWORD PTR [ebp+416], eax
	mov eax, 2118320456
	mov DWORD PTR [ebp+420], eax
	mov eax, 328286178
	mov DWORD PTR [ebp+424], eax
	mov eax, 445110887
	mov DWORD PTR [ebp+428], eax
	mov eax, 2054594582
	mov DWORD PTR [ebp+432], eax
	mov eax, -877350605
	mov DWORD PTR [ebp+436], eax
	mov eax, -930584828
	mov DWORD PTR [ebp+512], eax
	mov eax, -238960028
	mov DWORD PTR [ebp+516], eax
	mov eax, -983310457
	mov DWORD PTR [ebp+520], eax
	mov eax, 1099921762
	mov DWORD PTR [ebp+524], eax
	mov eax, -1163750934
	mov DWORD PTR [ebp+528], eax
	mov eax, -702716183
	mov DWORD PTR [ebp+532], eax
	mov eax, -1848981984
	mov DWORD PTR [ebp+536], eax
	mov eax, -14370353
	mov DWORD PTR [ebp+540], eax
	mov eax, 650815121
	mov DWORD PTR [ebp+544], eax
	mov eax, -927176243
	mov DWORD PTR [ebp+548], eax
	mov eax, -976292479
	mov DWORD PTR [ebp+552], eax
	mov eax, 125794213
	mov DWORD PTR [ebp+556], eax
	mov eax, -463403115
	mov DWORD PTR [ebp+560], eax
	mov eax, -863109553
	mov DWORD PTR [ebp+564], eax
	mov eax, 1
	mov DWORD PTR [ebp+640], eax
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
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_X448_COMB}
	pop ecx
	mov DWORD PTR [edi+4096], eax
	mov esi, 0
22:
	mov ebp, esi
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edi
	movzx ecx, BYTE PTR [ebp+3079]
	movzx eax, BYTE PTR [ebp+3078]
	add ecx, ecx
	add ecx, eax
	movzx eax, BYTE PTR [ebp+3077]
	add ecx, ecx
	add ecx, eax
	movzx eax, BYTE PTR [ebp+3076]
	add ecx, ecx
	add ecx, eax
	sub ecx, 8
	mov eax, ecx
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	xor ecx, ebx
	sub ecx, ebx
	mov eax, esi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ebp, DWORD PTR [edi+4096]
	add ebp, eax
	add ebp, eax
	add ebp, eax
	add ebp, eax
	add ebp, eax
	add ebp, eax
	add ebp, eax
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
	and ebx, 1
	mov DWORD PTR [edi+1216], ebx
	mov eax, ecx
	xor eax, 1
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp]
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+4]
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+8]
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+12]
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+16]
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+20]
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+24]
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+28]
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+32]
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+36]
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+40]
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+44]
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+48]
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+52]
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+448]
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+452]
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+456]
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+460]
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+464]
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+468]
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+472]
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+476]
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+480]
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+484]
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+488]
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+492]
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+496]
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+500]
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 2
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+56]
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+60]
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+68]
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+72]
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+76]
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+80]
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+84]
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+88]
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+92]
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+96]
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+100]
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+104]
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+108]
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+504]
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+508]
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+512]
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+516]
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+520]
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+524]
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+528]
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+532]
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+536]
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+540]
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+544]
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+548]
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+552]
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+556]
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 3
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+112]
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+116]
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+120]
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+124]
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+128]
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+132]
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+136]
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+140]
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+144]
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+148]
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+152]
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+156]
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+160]
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+164]
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+560]
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+564]
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+568]
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+572]
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+576]
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+580]
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+584]
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+588]
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+592]
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+596]
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+600]
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+604]
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+608]
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+612]
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 4
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+168]
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+172]
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+176]
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+180]
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+184]
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+188]
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+192]
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+196]
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+200]
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+204]
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+208]
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+212]
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+216]
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+220]
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+616]
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+620]
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+624]
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+628]
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+632]
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+636]
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+640]
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+644]
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+648]
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+652]
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+656]
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+660]
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+664]
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+668]
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 5
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+224]
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+228]
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+232]
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+236]
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+240]
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+244]
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+248]
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+252]
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+256]
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+260]
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+264]
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+268]
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+272]
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+276]
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+672]
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+676]
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+680]
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+684]
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+688]
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+692]
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+696]
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+700]
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+704]
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+708]
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+712]
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+716]
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+720]
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+724]
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 6
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+280]
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+284]
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+288]
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+292]
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+296]
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+300]
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+304]
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+308]
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+312]
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+316]
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+320]
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+324]
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+328]
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+332]
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+728]
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+732]
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+736]
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+740]
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+744]
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+748]
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+752]
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+756]
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+760]
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+764]
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+768]
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+772]
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+776]
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+780]
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 7
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+336]
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+340]
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+344]
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+348]
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+352]
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+356]
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+360]
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+364]
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+368]
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+372]
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+376]
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+380]
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+384]
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+388]
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+784]
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+788]
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+792]
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+796]
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+800]
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+804]
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+808]
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+812]
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+816]
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+820]
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+824]
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+828]
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+832]
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+836]
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 8
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+392]
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+396]
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+400]
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+404]
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+408]
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+412]
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+416]
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+420]
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+424]
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+428]
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+432]
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+436]
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+440]
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+444]
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+840]
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+844]
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+848]
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+852]
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+856]
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+860]
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+864]
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+868]
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+872]
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+876]
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+880]
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+884]
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+888]
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+892]
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 1600
	mov ecx, 2752
	mov edx, 1088
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, esi
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edi
	movzx ebx, BYTE PTR [ebp+3079]
	sub ebx, 1
	mov eax, DWORD PTR [edi+1088]
	mov ecx, DWORD PTR [edi+1600]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1088], eax
	mov DWORD PTR [edi+1600], ecx
	mov eax, DWORD PTR [edi+1092]
	mov ecx, DWORD PTR [edi+1604]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1092], eax
	mov DWORD PTR [edi+1604], ecx
	mov eax, DWORD PTR [edi+1096]
	mov ecx, DWORD PTR [edi+1608]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1096], eax
	mov DWORD PTR [edi+1608], ecx
	mov eax, DWORD PTR [edi+1100]
	mov ecx, DWORD PTR [edi+1612]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1100], eax
	mov DWORD PTR [edi+1612], ecx
	mov eax, DWORD PTR [edi+1104]
	mov ecx, DWORD PTR [edi+1616]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1104], eax
	mov DWORD PTR [edi+1616], ecx
	mov eax, DWORD PTR [edi+1108]
	mov ecx, DWORD PTR [edi+1620]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1108], eax
	mov DWORD PTR [edi+1620], ecx
	mov eax, DWORD PTR [edi+1112]
	mov ecx, DWORD PTR [edi+1624]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1112], eax
	mov DWORD PTR [edi+1624], ecx
	mov eax, DWORD PTR [edi+1116]
	mov ecx, DWORD PTR [edi+1628]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1116], eax
	mov DWORD PTR [edi+1628], ecx
	mov eax, DWORD PTR [edi+1120]
	mov ecx, DWORD PTR [edi+1632]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1120], eax
	mov DWORD PTR [edi+1632], ecx
	mov eax, DWORD PTR [edi+1124]
	mov ecx, DWORD PTR [edi+1636]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1124], eax
	mov DWORD PTR [edi+1636], ecx
	mov eax, DWORD PTR [edi+1128]
	mov ecx, DWORD PTR [edi+1640]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1128], eax
	mov DWORD PTR [edi+1640], ecx
	mov eax, DWORD PTR [edi+1132]
	mov ecx, DWORD PTR [edi+1644]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1132], eax
	mov DWORD PTR [edi+1644], ecx
	mov eax, DWORD PTR [edi+1136]
	mov ecx, DWORD PTR [edi+1648]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1136], eax
	mov DWORD PTR [edi+1648], ecx
	mov eax, DWORD PTR [edi+1140]
	mov ecx, DWORD PTR [edi+1652]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1140], eax
	mov DWORD PTR [edi+1652], ecx
	mov eax, 1600
	mov ecx, 320
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1728
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
	mov eax, 1856
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
	mov eax, 1984
	mov ecx, 1728
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
	mov eax, 1984
	mov ecx, 1984
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul_a24}
	pop eax
	pop eax
	pop eax
	mov eax, 2112
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
	mov eax, 2240
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
	mov eax, 2112
	mov ecx, 2112
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
	mov eax, 2112
	mov ecx, 2112
	mov edx, 1728
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 2112
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
	mov eax, 2240
	mov ecx, 1856
	mov edx, 1728
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
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
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
	mov eax, 1728
	mov ecx, 320
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
	mov eax, 64
	mov ecx, 1728
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
	mov eax, 1728
	mov ecx, 320
	mov edx, 1600
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
	mov ecx, 1728
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
	mov eax, 320
	mov ecx, 2368
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, esi
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edi
	movzx ecx, BYTE PTR [ebp+3075]
	movzx eax, BYTE PTR [ebp+3074]
	add ecx, ecx
	add ecx, eax
	movzx eax, BYTE PTR [ebp+3073]
	add ecx, ecx
	add ecx, eax
	movzx eax, BYTE PTR [ebp+3072]
	add ecx, ecx
	add ecx, eax
	sub ecx, 8
	mov eax, ecx
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	xor ecx, ebx
	sub ecx, ebx
	mov eax, esi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ebp, DWORD PTR [edi+4096]
	add ebp, eax
	add ebp, eax
	add ebp, eax
	add ebp, eax
	add ebp, eax
	add ebp, eax
	add ebp, eax
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
	and ebx, 1
	mov DWORD PTR [edi+1216], ebx
	mov eax, ecx
	xor eax, 1
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp]
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+4]
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+8]
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+12]
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+16]
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+20]
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+24]
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+28]
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+32]
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+36]
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+40]
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+44]
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+48]
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+52]
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+448]
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+452]
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+456]
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+460]
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+464]
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+468]
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+472]
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+476]
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+480]
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+484]
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+488]
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+492]
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+496]
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+500]
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 2
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+56]
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+60]
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+68]
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+72]
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+76]
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+80]
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+84]
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+88]
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+92]
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+96]
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+100]
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+104]
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+108]
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+504]
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+508]
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+512]
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+516]
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+520]
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+524]
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+528]
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+532]
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+536]
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+540]
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+544]
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+548]
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+552]
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+556]
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 3
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+112]
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+116]
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+120]
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+124]
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+128]
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+132]
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+136]
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+140]
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+144]
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+148]
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+152]
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+156]
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+160]
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+164]
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+560]
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+564]
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+568]
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+572]
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+576]
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+580]
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+584]
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+588]
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+592]
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+596]
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+600]
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+604]
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+608]
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+612]
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 4
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+168]
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+172]
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+176]
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+180]
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+184]
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+188]
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+192]
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+196]
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+200]
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+204]
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+208]
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+212]
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+216]
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+220]
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+616]
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+620]
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+624]
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+628]
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+632]
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+636]
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+640]
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+644]
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+648]
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+652]
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+656]
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+660]
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+664]
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+668]
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 5
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+224]
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+228]
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+232]
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+236]
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+240]
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+244]
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+248]
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+252]
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+256]
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+260]
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+264]
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+268]
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+272]
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+276]
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+672]
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+676]
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+680]
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+684]
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+688]
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+692]
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+696]
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+700]
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+704]
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+708]
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+712]
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+716]
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+720]
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+724]
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 6
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+280]
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+284]
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+288]
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+292]
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+296]
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+300]
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+304]
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+308]
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+312]
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+316]
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+320]
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+324]
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+328]
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+332]
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+728]
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+732]
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+736]
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+740]
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+744]
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+748]
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+752]
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+756]
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+760]
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+764]
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+768]
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+772]
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+776]
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+780]
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 7
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+336]
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+340]
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+344]
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+348]
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+352]
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+356]
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+360]
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+364]
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+368]
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+372]
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+376]
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+380]
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+384]
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+388]
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+784]
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+788]
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+792]
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+796]
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+800]
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+804]
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+808]
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+812]
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+816]
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+820]
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+824]
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+828]
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+832]
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+836]
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, ecx
	xor eax, 8
	sub eax, 1
	shr eax, 31
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+392]
	and eax, ebx
	or eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [ebp+396]
	and eax, ebx
	or eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [ebp+400]
	and eax, ebx
	or eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [ebp+404]
	and eax, ebx
	or eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [ebp+408]
	and eax, ebx
	or eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [ebp+412]
	and eax, ebx
	or eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [ebp+416]
	and eax, ebx
	or eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [ebp+420]
	and eax, ebx
	or eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [ebp+424]
	and eax, ebx
	or eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [ebp+428]
	and eax, ebx
	or eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [ebp+432]
	and eax, ebx
	or eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [ebp+436]
	and eax, ebx
	or eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [ebp+440]
	and eax, ebx
	or eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [ebp+444]
	and eax, ebx
	or eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [ebp+840]
	and eax, ebx
	or eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [ebp+844]
	and eax, ebx
	or eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [ebp+848]
	and eax, ebx
	or eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [ebp+852]
	and eax, ebx
	or eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [ebp+856]
	and eax, ebx
	or eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [ebp+860]
	and eax, ebx
	or eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [ebp+864]
	and eax, ebx
	or eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [ebp+868]
	and eax, ebx
	or eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [ebp+872]
	and eax, ebx
	or eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [ebp+876]
	and eax, ebx
	or eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [ebp+880]
	and eax, ebx
	or eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [ebp+884]
	and eax, ebx
	or eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [ebp+888]
	and eax, ebx
	or eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [ebp+892]
	and eax, ebx
	or eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1268], eax
	mov eax, 1600
	mov ecx, 2752
	mov edx, 1088
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, esi
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edi
	movzx ebx, BYTE PTR [ebp+3075]
	sub ebx, 1
	mov eax, DWORD PTR [edi+1088]
	mov ecx, DWORD PTR [edi+1600]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1088], eax
	mov DWORD PTR [edi+1600], ecx
	mov eax, DWORD PTR [edi+1092]
	mov ecx, DWORD PTR [edi+1604]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1092], eax
	mov DWORD PTR [edi+1604], ecx
	mov eax, DWORD PTR [edi+1096]
	mov ecx, DWORD PTR [edi+1608]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1096], eax
	mov DWORD PTR [edi+1608], ecx
	mov eax, DWORD PTR [edi+1100]
	mov ecx, DWORD PTR [edi+1612]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1100], eax
	mov DWORD PTR [edi+1612], ecx
	mov eax, DWORD PTR [edi+1104]
	mov ecx, DWORD PTR [edi+1616]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1104], eax
	mov DWORD PTR [edi+1616], ecx
	mov eax, DWORD PTR [edi+1108]
	mov ecx, DWORD PTR [edi+1620]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1108], eax
	mov DWORD PTR [edi+1620], ecx
	mov eax, DWORD PTR [edi+1112]
	mov ecx, DWORD PTR [edi+1624]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1112], eax
	mov DWORD PTR [edi+1624], ecx
	mov eax, DWORD PTR [edi+1116]
	mov ecx, DWORD PTR [edi+1628]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1116], eax
	mov DWORD PTR [edi+1628], ecx
	mov eax, DWORD PTR [edi+1120]
	mov ecx, DWORD PTR [edi+1632]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1120], eax
	mov DWORD PTR [edi+1632], ecx
	mov eax, DWORD PTR [edi+1124]
	mov ecx, DWORD PTR [edi+1636]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1124], eax
	mov DWORD PTR [edi+1636], ecx
	mov eax, DWORD PTR [edi+1128]
	mov ecx, DWORD PTR [edi+1640]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1128], eax
	mov DWORD PTR [edi+1640], ecx
	mov eax, DWORD PTR [edi+1132]
	mov ecx, DWORD PTR [edi+1644]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1132], eax
	mov DWORD PTR [edi+1644], ecx
	mov eax, DWORD PTR [edi+1136]
	mov ecx, DWORD PTR [edi+1648]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1136], eax
	mov DWORD PTR [edi+1648], ecx
	mov eax, DWORD PTR [edi+1140]
	mov ecx, DWORD PTR [edi+1652]
	mov edx, eax
	xor edx, ecx
	and edx, ebx
	xor eax, edx
	xor ecx, edx
	mov DWORD PTR [edi+1140], eax
	mov DWORD PTR [edi+1652], ecx
	mov eax, 1600
	mov ecx, 704
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 1728
	mov ecx, 448
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
	mov eax, 1856
	mov ecx, 576
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
	mov eax, 1984
	mov ecx, 1728
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
	mov eax, 1984
	mov ecx, 1984
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul_a24}
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 448
	mov edx, 576
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
	mov eax, 2112
	mov ecx, 2112
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
	mov eax, 2112
	mov ecx, 2112
	mov edx, 1728
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sub}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2112
	mov ecx, 2112
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
	mov eax, 2240
	mov ecx, 1856
	mov edx, 1728
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
	call {vg_gf448_r32_add}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
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
	mov eax, 1728
	mov ecx, 704
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
	mov eax, 448
	mov ecx, 1728
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
	mov eax, 1728
	mov ecx, 704
	mov edx, 1600
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
	mov ecx, 1728
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
	mov eax, 704
	mov ecx, 2368
	mov edx, 1600
	push edx
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	add esi, 1
	cmp esi, 57
	jne 22b
	mov esi, 4
23:
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
	sub esi, 1
	jne 23b
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [edi+1268], eax
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+1344], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+1348], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+1352], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+1356], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+1360], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+1364], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [edi+1368], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [edi+1372], eax
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [edi+1376], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [edi+1380], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [edi+1384], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [edi+1388], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [edi+1392], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [edi+1396], eax
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
	mov eax, 320
	mov ecx, 64
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
	pop eax
	pop eax
	pop eax
	mov eax, 192
	mov ecx, 192
	push ecx
	push eax
	push edi
	call {vg_gf448_r32_sqr}
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
	mov esi, 1
24:
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
	jne 24b
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
25:
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
	jne 25b
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
26:
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
	jne 26b
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
27:
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
	jne 27b
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
28:
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
	jne 28b
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
29:
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
	jne 29b
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
	mov esi, 64
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
215:
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
	jne 215b
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
217:
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
	jne 217b
	mov esi, 2
218:
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
	jne 218b
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
	mov eax, 192
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
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-20]
	movdqu XMMWORD PTR [esp], xmm0
	mov DWORD PTR [esp+16], ecx
	lea esp, [esp+20]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6
