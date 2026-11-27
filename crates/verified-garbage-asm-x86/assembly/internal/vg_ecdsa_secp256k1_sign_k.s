// The functions of `src/internal/vg_ecdsa_secp256k1_sign_k.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_secp256k1_sign_k:
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SECP256K1_COMB}
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
	mov eax, -977
	mov DWORD PTR [edi+64], eax
	mov eax, -2
	mov DWORD PTR [edi+68], eax
	mov eax, -1
	mov DWORD PTR [edi+72], eax
	mov eax, -1
	mov DWORD PTR [edi+76], eax
	mov eax, -1
	mov DWORD PTR [edi+80], eax
	mov eax, -1
	mov DWORD PTR [edi+84], eax
	mov eax, -1
	mov DWORD PTR [edi+88], eax
	mov eax, -1
	mov DWORD PTR [edi+92], eax
	mov eax, -801750719
	mov DWORD PTR [edi+96], eax
	mov eax, -1076732276
	mov DWORD PTR [edi+100], eax
	mov eax, -1354194885
	mov DWORD PTR [edi+104], eax
	mov eax, -1162945306
	mov DWORD PTR [edi+108], eax
	mov eax, -2
	mov DWORD PTR [edi+112], eax
	mov eax, -1
	mov DWORD PTR [edi+116], eax
	mov eax, -1
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
	mov eax, 977
	mov DWORD PTR [edi+224], eax
	mov eax, 1
	mov DWORD PTR [edi+228], eax
	mov eax, 0
	mov DWORD PTR [edi+232], eax
	mov eax, 0
	mov DWORD PTR [edi+236], eax
	mov eax, 0
	mov DWORD PTR [edi+240], eax
	mov eax, 0
	mov DWORD PTR [edi+244], eax
	mov eax, 0
	mov DWORD PTR [edi+248], eax
	mov eax, 0
	mov DWORD PTR [edi+252], eax
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
	mov eax, 20517
	mov DWORD PTR [edi+288], eax
	mov eax, 21
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
	mov eax, 1216225431
	mov DWORD PTR [edi+320], eax
	mov eax, -684315046
	mov DWORD PTR [edi+324], eax
	mov eax, 700212955
	mov DWORD PTR [edi+328], eax
	mov eax, 589179219
	mov DWORD PTR [edi+332], eax
	mov eax, 872223388
	mov DWORD PTR [edi+336], eax
	mov eax, -1751168832
	mov DWORD PTR [edi+340], eax
	mov eax, -385310904
	mov DWORD PTR [edi+344], eax
	mov eax, -1719540157
	mov DWORD PTR [edi+348], eax
	mov eax, -740578334
	mov DWORD PTR [edi+352], eax
	mov eax, -1319196974
	mov DWORD PTR [edi+356], eax
	mov eax, 522045005
	mov DWORD PTR [edi+360], eax
	mov eax, -1912840867
	mov DWORD PTR [edi+364], eax
	mov eax, -1407598282
	mov DWORD PTR [edi+368], eax
	mov eax, 1891022234
	mov DWORD PTR [edi+372], eax
	mov eax, -727350570
	mov DWORD PTR [edi+376], eax
	mov eax, -817920737
	mov DWORD PTR [edi+380], eax
	mov eax, 1742197056
	mov DWORD PTR [edi+384], eax
	mov eax, -1989348844
	mov DWORD PTR [edi+388], eax
	mov eax, 243071096
	mov DWORD PTR [edi+392], eax
	mov eax, 1947506370
	mov DWORD PTR [edi+396], eax
	mov eax, 1540163526
	mov DWORD PTR [edi+400], eax
	mov eax, -426248732
	mov DWORD PTR [edi+404], eax
	mov eax, -2117690427
	mov DWORD PTR [edi+408], eax
	mov eax, -1654186795
	mov DWORD PTR [edi+412], eax
	mov eax, 801750719
	mov DWORD PTR [edi+416], eax
	mov eax, 1076732275
	mov DWORD PTR [edi+420], eax
	mov eax, 1354194884
	mov DWORD PTR [edi+424], eax
	mov eax, 1162945305
	mov DWORD PTR [edi+428], eax
	mov eax, 1
	mov DWORD PTR [edi+432], eax
	mov eax, 0
	mov DWORD PTR [edi+436], eax
	mov eax, 0
	mov DWORD PTR [edi+440], eax
	mov eax, 0
	mov DWORD PTR [edi+444], eax
	mov eax, -979
	mov DWORD PTR [edi+448], eax
	mov eax, -2
	mov DWORD PTR [edi+452], eax
	mov eax, -1
	mov DWORD PTR [edi+456], eax
	mov eax, -1
	mov DWORD PTR [edi+460], eax
	mov eax, -1
	mov DWORD PTR [edi+464], eax
	mov eax, -1
	mov DWORD PTR [edi+468], eax
	mov eax, -1
	mov DWORD PTR [edi+472], eax
	mov eax, -1
	mov DWORD PTR [edi+476], eax
	mov eax, -801750721
	mov DWORD PTR [edi+480], eax
	mov eax, -1076732276
	mov DWORD PTR [edi+484], eax
	mov eax, -1354194885
	mov DWORD PTR [edi+488], eax
	mov eax, -1162945306
	mov DWORD PTR [edi+492], eax
	mov eax, -2
	mov DWORD PTR [edi+496], eax
	mov eax, -1
	mov DWORD PTR [edi+500], eax
	mov eax, -1
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
	mov eax, 977
	mov DWORD PTR [edi+544], eax
	mov eax, 1
	mov DWORD PTR [edi+548], eax
	mov eax, 0
	mov DWORD PTR [edi+552], eax
	mov eax, 0
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
	call {vg_secp256k1_comb}
	call {vg_secp256k1_inv_mod_p}
	mov eax, 992
	mov ecx, 512
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
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
	call {vg_secp256k1_mul_mod_p}
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
	call {vg_secp256k1_add_mod_n}
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
	call {vg_secp256k1_mul_mod_n}
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
	call {vg_secp256k1_inv_mod_n}
	mov eax, 384
	mov ecx, 1216
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_n}
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
	call {vg_secp256k1_mul_mod_n}
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
	call {vg_secp256k1_mul_mod_n}
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
	call {vg_secp256k1_mul_mod_n}
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
	call {vg_secp256k1_add_mod_n}
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
	call {vg_secp256k1_mul_mod_n}
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
	call {vg_secp256k1_mul_mod_n}
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
