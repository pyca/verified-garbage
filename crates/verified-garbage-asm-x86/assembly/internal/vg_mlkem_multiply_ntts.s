// The functions of `src/internal/vg_mlkem_multiply_ntts.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_multiply_ntts:
	push ebx
	push esi
	push edi
	push ebp
	mov eax, DWORD PTR [esp+32]
	mov edx, 17
	mov DWORD PTR [eax], edx
	mov edx, 3312
	mov DWORD PTR [eax+4], edx
	mov edx, 2761
	mov DWORD PTR [eax+8], edx
	mov edx, 568
	mov DWORD PTR [eax+12], edx
	mov edx, 583
	mov DWORD PTR [eax+16], edx
	mov edx, 2746
	mov DWORD PTR [eax+20], edx
	mov edx, 2649
	mov DWORD PTR [eax+24], edx
	mov edx, 680
	mov DWORD PTR [eax+28], edx
	mov edx, 1637
	mov DWORD PTR [eax+32], edx
	mov edx, 1692
	mov DWORD PTR [eax+36], edx
	mov edx, 723
	mov DWORD PTR [eax+40], edx
	mov edx, 2606
	mov DWORD PTR [eax+44], edx
	mov edx, 2288
	mov DWORD PTR [eax+48], edx
	mov edx, 1041
	mov DWORD PTR [eax+52], edx
	mov edx, 1100
	mov DWORD PTR [eax+56], edx
	mov edx, 2229
	mov DWORD PTR [eax+60], edx
	mov edx, 1409
	mov DWORD PTR [eax+64], edx
	mov edx, 1920
	mov DWORD PTR [eax+68], edx
	mov edx, 2662
	mov DWORD PTR [eax+72], edx
	mov edx, 667
	mov DWORD PTR [eax+76], edx
	mov edx, 3281
	mov DWORD PTR [eax+80], edx
	mov edx, 48
	mov DWORD PTR [eax+84], edx
	mov edx, 233
	mov DWORD PTR [eax+88], edx
	mov edx, 3096
	mov DWORD PTR [eax+92], edx
	mov edx, 756
	mov DWORD PTR [eax+96], edx
	mov edx, 2573
	mov DWORD PTR [eax+100], edx
	mov edx, 2156
	mov DWORD PTR [eax+104], edx
	mov edx, 1173
	mov DWORD PTR [eax+108], edx
	mov edx, 3015
	mov DWORD PTR [eax+112], edx
	mov edx, 314
	mov DWORD PTR [eax+116], edx
	mov edx, 3050
	mov DWORD PTR [eax+120], edx
	mov edx, 279
	mov DWORD PTR [eax+124], edx
	mov edx, 1703
	mov DWORD PTR [eax+128], edx
	mov edx, 1626
	mov DWORD PTR [eax+132], edx
	mov edx, 1651
	mov DWORD PTR [eax+136], edx
	mov edx, 1678
	mov DWORD PTR [eax+140], edx
	mov edx, 2789
	mov DWORD PTR [eax+144], edx
	mov edx, 540
	mov DWORD PTR [eax+148], edx
	mov edx, 1789
	mov DWORD PTR [eax+152], edx
	mov edx, 1540
	mov DWORD PTR [eax+156], edx
	mov edx, 1847
	mov DWORD PTR [eax+160], edx
	mov edx, 1482
	mov DWORD PTR [eax+164], edx
	mov edx, 952
	mov DWORD PTR [eax+168], edx
	mov edx, 2377
	mov DWORD PTR [eax+172], edx
	mov edx, 1461
	mov DWORD PTR [eax+176], edx
	mov edx, 1868
	mov DWORD PTR [eax+180], edx
	mov edx, 2687
	mov DWORD PTR [eax+184], edx
	mov edx, 642
	mov DWORD PTR [eax+188], edx
	mov edx, 939
	mov DWORD PTR [eax+192], edx
	mov edx, 2390
	mov DWORD PTR [eax+196], edx
	mov edx, 2308
	mov DWORD PTR [eax+200], edx
	mov edx, 1021
	mov DWORD PTR [eax+204], edx
	mov edx, 2437
	mov DWORD PTR [eax+208], edx
	mov edx, 892
	mov DWORD PTR [eax+212], edx
	mov edx, 2388
	mov DWORD PTR [eax+216], edx
	mov edx, 941
	mov DWORD PTR [eax+220], edx
	mov edx, 733
	mov DWORD PTR [eax+224], edx
	mov edx, 2596
	mov DWORD PTR [eax+228], edx
	mov edx, 2337
	mov DWORD PTR [eax+232], edx
	mov edx, 992
	mov DWORD PTR [eax+236], edx
	mov edx, 268
	mov DWORD PTR [eax+240], edx
	mov edx, 3061
	mov DWORD PTR [eax+244], edx
	mov edx, 641
	mov DWORD PTR [eax+248], edx
	mov edx, 2688
	mov DWORD PTR [eax+252], edx
	mov edx, 1584
	mov DWORD PTR [eax+256], edx
	mov edx, 1745
	mov DWORD PTR [eax+260], edx
	mov edx, 2298
	mov DWORD PTR [eax+264], edx
	mov edx, 1031
	mov DWORD PTR [eax+268], edx
	mov edx, 2037
	mov DWORD PTR [eax+272], edx
	mov edx, 1292
	mov DWORD PTR [eax+276], edx
	mov edx, 3220
	mov DWORD PTR [eax+280], edx
	mov edx, 109
	mov DWORD PTR [eax+284], edx
	mov edx, 375
	mov DWORD PTR [eax+288], edx
	mov edx, 2954
	mov DWORD PTR [eax+292], edx
	mov edx, 2549
	mov DWORD PTR [eax+296], edx
	mov edx, 780
	mov DWORD PTR [eax+300], edx
	mov edx, 2090
	mov DWORD PTR [eax+304], edx
	mov edx, 1239
	mov DWORD PTR [eax+308], edx
	mov edx, 1645
	mov DWORD PTR [eax+312], edx
	mov edx, 1684
	mov DWORD PTR [eax+316], edx
	mov edx, 1063
	mov DWORD PTR [eax+320], edx
	mov edx, 2266
	mov DWORD PTR [eax+324], edx
	mov edx, 319
	mov DWORD PTR [eax+328], edx
	mov edx, 3010
	mov DWORD PTR [eax+332], edx
	mov edx, 2773
	mov DWORD PTR [eax+336], edx
	mov edx, 556
	mov DWORD PTR [eax+340], edx
	mov edx, 757
	mov DWORD PTR [eax+344], edx
	mov edx, 2572
	mov DWORD PTR [eax+348], edx
	mov edx, 2099
	mov DWORD PTR [eax+352], edx
	mov edx, 1230
	mov DWORD PTR [eax+356], edx
	mov edx, 561
	mov DWORD PTR [eax+360], edx
	mov edx, 2768
	mov DWORD PTR [eax+364], edx
	mov edx, 2466
	mov DWORD PTR [eax+368], edx
	mov edx, 863
	mov DWORD PTR [eax+372], edx
	mov edx, 2594
	mov DWORD PTR [eax+376], edx
	mov edx, 735
	mov DWORD PTR [eax+380], edx
	mov edx, 2804
	mov DWORD PTR [eax+384], edx
	mov edx, 525
	mov DWORD PTR [eax+388], edx
	mov edx, 1092
	mov DWORD PTR [eax+392], edx
	mov edx, 2237
	mov DWORD PTR [eax+396], edx
	mov edx, 403
	mov DWORD PTR [eax+400], edx
	mov edx, 2926
	mov DWORD PTR [eax+404], edx
	mov edx, 1026
	mov DWORD PTR [eax+408], edx
	mov edx, 2303
	mov DWORD PTR [eax+412], edx
	mov edx, 1143
	mov DWORD PTR [eax+416], edx
	mov edx, 2186
	mov DWORD PTR [eax+420], edx
	mov edx, 2150
	mov DWORD PTR [eax+424], edx
	mov edx, 1179
	mov DWORD PTR [eax+428], edx
	mov edx, 2775
	mov DWORD PTR [eax+432], edx
	mov edx, 554
	mov DWORD PTR [eax+436], edx
	mov edx, 886
	mov DWORD PTR [eax+440], edx
	mov edx, 2443
	mov DWORD PTR [eax+444], edx
	mov edx, 1722
	mov DWORD PTR [eax+448], edx
	mov edx, 1607
	mov DWORD PTR [eax+452], edx
	mov edx, 1212
	mov DWORD PTR [eax+456], edx
	mov edx, 2117
	mov DWORD PTR [eax+460], edx
	mov edx, 1874
	mov DWORD PTR [eax+464], edx
	mov edx, 1455
	mov DWORD PTR [eax+468], edx
	mov edx, 1029
	mov DWORD PTR [eax+472], edx
	mov edx, 2300
	mov DWORD PTR [eax+476], edx
	mov edx, 2110
	mov DWORD PTR [eax+480], edx
	mov edx, 1219
	mov DWORD PTR [eax+484], edx
	mov edx, 2935
	mov DWORD PTR [eax+488], edx
	mov edx, 394
	mov DWORD PTR [eax+492], edx
	mov edx, 885
	mov DWORD PTR [eax+496], edx
	mov edx, 2444
	mov DWORD PTR [eax+500], edx
	mov edx, 2154
	mov DWORD PTR [eax+504], edx
	mov edx, 1175
	mov DWORD PTR [eax+508], edx
	mov ebp, eax
	mov ebx, DWORD PTR [esp+20]
	mov edx, ebx
	add edx, 1024
	mov DWORD PTR [esp+32], edx
	mov esi, DWORD PTR [esp+24]
	mov edi, DWORD PTR [esp+28]
20:
	mov eax, DWORD PTR [esi+4]
	mov edx, DWORD PTR [edi+4]
	mul edx
	mov ecx, eax
	mov edx, 1290167
	mul edx
	mov eax, 3329
	mul edx
	sub ecx, eax
	sub ecx, 3329
	sbb edx, edx
	and edx, 3329
	add ecx, edx
	mov eax, ecx
	mov edx, DWORD PTR [ebp]
	mul edx
	mov ecx, eax
	mov eax, DWORD PTR [esi]
	mov edx, DWORD PTR [edi]
	mul edx
	add ecx, eax
	mov eax, ecx
	mov edx, 1290167
	mul edx
	mov eax, 3329
	mul edx
	sub ecx, eax
	sub ecx, 3329
	sbb edx, edx
	and edx, 3329
	add ecx, edx
	mov DWORD PTR [ebx], ecx
	mov eax, DWORD PTR [esi]
	mov edx, DWORD PTR [edi+4]
	mul edx
	mov ecx, eax
	mov eax, DWORD PTR [esi+4]
	mov edx, DWORD PTR [edi]
	mul edx
	add ecx, eax
	mov eax, ecx
	mov edx, 1290167
	mul edx
	mov eax, 3329
	mul edx
	sub ecx, eax
	sub ecx, 3329
	sbb edx, edx
	and edx, 3329
	add ecx, edx
	mov DWORD PTR [ebx+4], ecx
	add ebx, 8
	add esi, 8
	add edi, 8
	add ebp, 4
	cmp ebx, DWORD PTR [esp+32]
	jne 20b
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
