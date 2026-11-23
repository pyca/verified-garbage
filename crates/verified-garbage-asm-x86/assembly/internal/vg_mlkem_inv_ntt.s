// The functions of `src/internal/vg_mlkem_inv_ntt.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_inv_ntt:
	push ebx
	push esi
	push edi
	push ebp
	mov eax, DWORD PTR [esp+24]
	mov edx, 1
	mov DWORD PTR [eax], edx
	mov edx, 1729
	mov DWORD PTR [eax+4], edx
	mov edx, 2580
	mov DWORD PTR [eax+8], edx
	mov edx, 3289
	mov DWORD PTR [eax+12], edx
	mov edx, 2642
	mov DWORD PTR [eax+16], edx
	mov edx, 630
	mov DWORD PTR [eax+20], edx
	mov edx, 1897
	mov DWORD PTR [eax+24], edx
	mov edx, 848
	mov DWORD PTR [eax+28], edx
	mov edx, 1062
	mov DWORD PTR [eax+32], edx
	mov edx, 1919
	mov DWORD PTR [eax+36], edx
	mov edx, 193
	mov DWORD PTR [eax+40], edx
	mov edx, 797
	mov DWORD PTR [eax+44], edx
	mov edx, 2786
	mov DWORD PTR [eax+48], edx
	mov edx, 3260
	mov DWORD PTR [eax+52], edx
	mov edx, 569
	mov DWORD PTR [eax+56], edx
	mov edx, 1746
	mov DWORD PTR [eax+60], edx
	mov edx, 296
	mov DWORD PTR [eax+64], edx
	mov edx, 2447
	mov DWORD PTR [eax+68], edx
	mov edx, 1339
	mov DWORD PTR [eax+72], edx
	mov edx, 1476
	mov DWORD PTR [eax+76], edx
	mov edx, 3046
	mov DWORD PTR [eax+80], edx
	mov edx, 56
	mov DWORD PTR [eax+84], edx
	mov edx, 2240
	mov DWORD PTR [eax+88], edx
	mov edx, 1333
	mov DWORD PTR [eax+92], edx
	mov edx, 1426
	mov DWORD PTR [eax+96], edx
	mov edx, 2094
	mov DWORD PTR [eax+100], edx
	mov edx, 535
	mov DWORD PTR [eax+104], edx
	mov edx, 2882
	mov DWORD PTR [eax+108], edx
	mov edx, 2393
	mov DWORD PTR [eax+112], edx
	mov edx, 2879
	mov DWORD PTR [eax+116], edx
	mov edx, 1974
	mov DWORD PTR [eax+120], edx
	mov edx, 821
	mov DWORD PTR [eax+124], edx
	mov edx, 289
	mov DWORD PTR [eax+128], edx
	mov edx, 331
	mov DWORD PTR [eax+132], edx
	mov edx, 3253
	mov DWORD PTR [eax+136], edx
	mov edx, 1756
	mov DWORD PTR [eax+140], edx
	mov edx, 1197
	mov DWORD PTR [eax+144], edx
	mov edx, 2304
	mov DWORD PTR [eax+148], edx
	mov edx, 2277
	mov DWORD PTR [eax+152], edx
	mov edx, 2055
	mov DWORD PTR [eax+156], edx
	mov edx, 650
	mov DWORD PTR [eax+160], edx
	mov edx, 1977
	mov DWORD PTR [eax+164], edx
	mov edx, 2513
	mov DWORD PTR [eax+168], edx
	mov edx, 632
	mov DWORD PTR [eax+172], edx
	mov edx, 2865
	mov DWORD PTR [eax+176], edx
	mov edx, 33
	mov DWORD PTR [eax+180], edx
	mov edx, 1320
	mov DWORD PTR [eax+184], edx
	mov edx, 1915
	mov DWORD PTR [eax+188], edx
	mov edx, 2319
	mov DWORD PTR [eax+192], edx
	mov edx, 1435
	mov DWORD PTR [eax+196], edx
	mov edx, 807
	mov DWORD PTR [eax+200], edx
	mov edx, 452
	mov DWORD PTR [eax+204], edx
	mov edx, 1438
	mov DWORD PTR [eax+208], edx
	mov edx, 2868
	mov DWORD PTR [eax+212], edx
	mov edx, 1534
	mov DWORD PTR [eax+216], edx
	mov edx, 2402
	mov DWORD PTR [eax+220], edx
	mov edx, 2647
	mov DWORD PTR [eax+224], edx
	mov edx, 2617
	mov DWORD PTR [eax+228], edx
	mov edx, 1481
	mov DWORD PTR [eax+232], edx
	mov edx, 648
	mov DWORD PTR [eax+236], edx
	mov edx, 2474
	mov DWORD PTR [eax+240], edx
	mov edx, 3110
	mov DWORD PTR [eax+244], edx
	mov edx, 1227
	mov DWORD PTR [eax+248], edx
	mov edx, 910
	mov DWORD PTR [eax+252], edx
	mov edx, 17
	mov DWORD PTR [eax+256], edx
	mov edx, 2761
	mov DWORD PTR [eax+260], edx
	mov edx, 583
	mov DWORD PTR [eax+264], edx
	mov edx, 2649
	mov DWORD PTR [eax+268], edx
	mov edx, 1637
	mov DWORD PTR [eax+272], edx
	mov edx, 723
	mov DWORD PTR [eax+276], edx
	mov edx, 2288
	mov DWORD PTR [eax+280], edx
	mov edx, 1100
	mov DWORD PTR [eax+284], edx
	mov edx, 1409
	mov DWORD PTR [eax+288], edx
	mov edx, 2662
	mov DWORD PTR [eax+292], edx
	mov edx, 3281
	mov DWORD PTR [eax+296], edx
	mov edx, 233
	mov DWORD PTR [eax+300], edx
	mov edx, 756
	mov DWORD PTR [eax+304], edx
	mov edx, 2156
	mov DWORD PTR [eax+308], edx
	mov edx, 3015
	mov DWORD PTR [eax+312], edx
	mov edx, 3050
	mov DWORD PTR [eax+316], edx
	mov edx, 1703
	mov DWORD PTR [eax+320], edx
	mov edx, 1651
	mov DWORD PTR [eax+324], edx
	mov edx, 2789
	mov DWORD PTR [eax+328], edx
	mov edx, 1789
	mov DWORD PTR [eax+332], edx
	mov edx, 1847
	mov DWORD PTR [eax+336], edx
	mov edx, 952
	mov DWORD PTR [eax+340], edx
	mov edx, 1461
	mov DWORD PTR [eax+344], edx
	mov edx, 2687
	mov DWORD PTR [eax+348], edx
	mov edx, 939
	mov DWORD PTR [eax+352], edx
	mov edx, 2308
	mov DWORD PTR [eax+356], edx
	mov edx, 2437
	mov DWORD PTR [eax+360], edx
	mov edx, 2388
	mov DWORD PTR [eax+364], edx
	mov edx, 733
	mov DWORD PTR [eax+368], edx
	mov edx, 2337
	mov DWORD PTR [eax+372], edx
	mov edx, 268
	mov DWORD PTR [eax+376], edx
	mov edx, 641
	mov DWORD PTR [eax+380], edx
	mov edx, 1584
	mov DWORD PTR [eax+384], edx
	mov edx, 2298
	mov DWORD PTR [eax+388], edx
	mov edx, 2037
	mov DWORD PTR [eax+392], edx
	mov edx, 3220
	mov DWORD PTR [eax+396], edx
	mov edx, 375
	mov DWORD PTR [eax+400], edx
	mov edx, 2549
	mov DWORD PTR [eax+404], edx
	mov edx, 2090
	mov DWORD PTR [eax+408], edx
	mov edx, 1645
	mov DWORD PTR [eax+412], edx
	mov edx, 1063
	mov DWORD PTR [eax+416], edx
	mov edx, 319
	mov DWORD PTR [eax+420], edx
	mov edx, 2773
	mov DWORD PTR [eax+424], edx
	mov edx, 757
	mov DWORD PTR [eax+428], edx
	mov edx, 2099
	mov DWORD PTR [eax+432], edx
	mov edx, 561
	mov DWORD PTR [eax+436], edx
	mov edx, 2466
	mov DWORD PTR [eax+440], edx
	mov edx, 2594
	mov DWORD PTR [eax+444], edx
	mov edx, 2804
	mov DWORD PTR [eax+448], edx
	mov edx, 1092
	mov DWORD PTR [eax+452], edx
	mov edx, 403
	mov DWORD PTR [eax+456], edx
	mov edx, 1026
	mov DWORD PTR [eax+460], edx
	mov edx, 1143
	mov DWORD PTR [eax+464], edx
	mov edx, 2150
	mov DWORD PTR [eax+468], edx
	mov edx, 2775
	mov DWORD PTR [eax+472], edx
	mov edx, 886
	mov DWORD PTR [eax+476], edx
	mov edx, 1722
	mov DWORD PTR [eax+480], edx
	mov edx, 1212
	mov DWORD PTR [eax+484], edx
	mov edx, 1874
	mov DWORD PTR [eax+488], edx
	mov edx, 1029
	mov DWORD PTR [eax+492], edx
	mov edx, 2110
	mov DWORD PTR [eax+496], edx
	mov edx, 2935
	mov DWORD PTR [eax+500], edx
	mov edx, 885
	mov DWORD PTR [eax+504], edx
	mov edx, 2154
	mov DWORD PTR [eax+508], edx
	mov ebp, eax
	add ebp, 508
	mov edx, DWORD PTR [esp+20]
	add edx, 1024
	mov DWORD PTR [esp+24], edx
	mov esi, DWORD PTR [esp+20]
20:
	mov edi, esi
	add edi, 8
	mov ecx, 2
21:
	mov ebx, DWORD PTR [edi]
	add ebx, 3329
	sub ebx, DWORD PTR [esi]
	mov eax, DWORD PTR [esi]
	add eax, DWORD PTR [edi]
	sub eax, 3329
	sbb edx, edx
	and edx, 3329
	add eax, edx
	mov DWORD PTR [esi], eax
	mov eax, ebx
	mov edx, DWORD PTR [ebp]
	mul edx
	mov ebx, eax
	mov edx, 1290167
	mul edx
	mov eax, 3329
	mul edx
	sub ebx, eax
	sub ebx, 3329
	sbb edx, edx
	and edx, 3329
	add ebx, edx
	mov DWORD PTR [edi], ebx
	add esi, 4
	add edi, 4
	sub ecx, 1
	jne 21b
	mov esi, edi
	sub ebp, 4
	cmp esi, DWORD PTR [esp+24]
	jne 20b
	mov esi, DWORD PTR [esp+20]
22:
	mov edi, esi
	add edi, 16
	mov ecx, 4
23:
	mov ebx, DWORD PTR [edi]
	add ebx, 3329
	sub ebx, DWORD PTR [esi]
	mov eax, DWORD PTR [esi]
	add eax, DWORD PTR [edi]
	sub eax, 3329
	sbb edx, edx
	and edx, 3329
	add eax, edx
	mov DWORD PTR [esi], eax
	mov eax, ebx
	mov edx, DWORD PTR [ebp]
	mul edx
	mov ebx, eax
	mov edx, 1290167
	mul edx
	mov eax, 3329
	mul edx
	sub ebx, eax
	sub ebx, 3329
	sbb edx, edx
	and edx, 3329
	add ebx, edx
	mov DWORD PTR [edi], ebx
	add esi, 4
	add edi, 4
	sub ecx, 1
	jne 23b
	mov esi, edi
	sub ebp, 4
	cmp esi, DWORD PTR [esp+24]
	jne 22b
	mov esi, DWORD PTR [esp+20]
24:
	mov edi, esi
	add edi, 32
	mov ecx, 8
25:
	mov ebx, DWORD PTR [edi]
	add ebx, 3329
	sub ebx, DWORD PTR [esi]
	mov eax, DWORD PTR [esi]
	add eax, DWORD PTR [edi]
	sub eax, 3329
	sbb edx, edx
	and edx, 3329
	add eax, edx
	mov DWORD PTR [esi], eax
	mov eax, ebx
	mov edx, DWORD PTR [ebp]
	mul edx
	mov ebx, eax
	mov edx, 1290167
	mul edx
	mov eax, 3329
	mul edx
	sub ebx, eax
	sub ebx, 3329
	sbb edx, edx
	and edx, 3329
	add ebx, edx
	mov DWORD PTR [edi], ebx
	add esi, 4
	add edi, 4
	sub ecx, 1
	jne 25b
	mov esi, edi
	sub ebp, 4
	cmp esi, DWORD PTR [esp+24]
	jne 24b
	mov esi, DWORD PTR [esp+20]
26:
	mov edi, esi
	add edi, 64
	mov ecx, 16
27:
	mov ebx, DWORD PTR [edi]
	add ebx, 3329
	sub ebx, DWORD PTR [esi]
	mov eax, DWORD PTR [esi]
	add eax, DWORD PTR [edi]
	sub eax, 3329
	sbb edx, edx
	and edx, 3329
	add eax, edx
	mov DWORD PTR [esi], eax
	mov eax, ebx
	mov edx, DWORD PTR [ebp]
	mul edx
	mov ebx, eax
	mov edx, 1290167
	mul edx
	mov eax, 3329
	mul edx
	sub ebx, eax
	sub ebx, 3329
	sbb edx, edx
	and edx, 3329
	add ebx, edx
	mov DWORD PTR [edi], ebx
	add esi, 4
	add edi, 4
	sub ecx, 1
	jne 27b
	mov esi, edi
	sub ebp, 4
	cmp esi, DWORD PTR [esp+24]
	jne 26b
	mov esi, DWORD PTR [esp+20]
28:
	mov edi, esi
	add edi, 128
	mov ecx, 32
29:
	mov ebx, DWORD PTR [edi]
	add ebx, 3329
	sub ebx, DWORD PTR [esi]
	mov eax, DWORD PTR [esi]
	add eax, DWORD PTR [edi]
	sub eax, 3329
	sbb edx, edx
	and edx, 3329
	add eax, edx
	mov DWORD PTR [esi], eax
	mov eax, ebx
	mov edx, DWORD PTR [ebp]
	mul edx
	mov ebx, eax
	mov edx, 1290167
	mul edx
	mov eax, 3329
	mul edx
	sub ebx, eax
	sub ebx, 3329
	sbb edx, edx
	and edx, 3329
	add ebx, edx
	mov DWORD PTR [edi], ebx
	add esi, 4
	add edi, 4
	sub ecx, 1
	jne 29b
	mov esi, edi
	sub ebp, 4
	cmp esi, DWORD PTR [esp+24]
	jne 28b
	mov esi, DWORD PTR [esp+20]
210:
	mov edi, esi
	add edi, 256
	mov ecx, 64
211:
	mov ebx, DWORD PTR [edi]
	add ebx, 3329
	sub ebx, DWORD PTR [esi]
	mov eax, DWORD PTR [esi]
	add eax, DWORD PTR [edi]
	sub eax, 3329
	sbb edx, edx
	and edx, 3329
	add eax, edx
	mov DWORD PTR [esi], eax
	mov eax, ebx
	mov edx, DWORD PTR [ebp]
	mul edx
	mov ebx, eax
	mov edx, 1290167
	mul edx
	mov eax, 3329
	mul edx
	sub ebx, eax
	sub ebx, 3329
	sbb edx, edx
	and edx, 3329
	add ebx, edx
	mov DWORD PTR [edi], ebx
	add esi, 4
	add edi, 4
	sub ecx, 1
	jne 211b
	mov esi, edi
	sub ebp, 4
	cmp esi, DWORD PTR [esp+24]
	jne 210b
	mov esi, DWORD PTR [esp+20]
212:
	mov edi, esi
	add edi, 512
	mov ecx, 128
213:
	mov ebx, DWORD PTR [edi]
	add ebx, 3329
	sub ebx, DWORD PTR [esi]
	mov eax, DWORD PTR [esi]
	add eax, DWORD PTR [edi]
	sub eax, 3329
	sbb edx, edx
	and edx, 3329
	add eax, edx
	mov DWORD PTR [esi], eax
	mov eax, ebx
	mov edx, DWORD PTR [ebp]
	mul edx
	mov ebx, eax
	mov edx, 1290167
	mul edx
	mov eax, 3329
	mul edx
	sub ebx, eax
	sub ebx, 3329
	sbb edx, edx
	and edx, 3329
	add ebx, edx
	mov DWORD PTR [edi], ebx
	add esi, 4
	add edi, 4
	sub ecx, 1
	jne 213b
	mov esi, edi
	sub ebp, 4
	cmp esi, DWORD PTR [esp+24]
	jne 212b
	mov esi, DWORD PTR [esp+20]
	mov ecx, 256
214:
	mov eax, DWORD PTR [esi]
	mov edx, 3303
	mul edx
	mov ebx, eax
	mov edx, 1290167
	mul edx
	mov eax, 3329
	mul edx
	sub ebx, eax
	sub ebx, 3329
	sbb edx, edx
	and edx, 3329
	add ebx, edx
	mov DWORD PTR [esi], ebx
	add esi, 4
	sub ecx, 1
	jne 214b
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
