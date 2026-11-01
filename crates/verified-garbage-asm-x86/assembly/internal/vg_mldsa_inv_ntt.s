// The functions of `src/internal/vg_mldsa_inv_ntt.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_inv_ntt:
	push ebx
	push esi
	push edi
	push ebp
	mov eax, DWORD PTR [esp+24]
	mov edx, 4186625
	mov DWORD PTR [eax], edx
	mov edx, 8354570
	mov DWORD PTR [eax+4], edx
	mov edx, 2608894
	mov DWORD PTR [eax+8], edx
	mov edx, 518909
	mov DWORD PTR [eax+12], edx
	mov edx, 8143293
	mov DWORD PTR [eax+16], edx
	mov edx, 777960
	mov DWORD PTR [eax+20], edx
	mov edx, 876248
	mov DWORD PTR [eax+24], edx
	mov edx, 7913949
	mov DWORD PTR [eax+28], edx
	mov edx, 6554070
	mov DWORD PTR [eax+32], edx
	mov edx, 6026966
	mov DWORD PTR [eax+36], edx
	mov edx, 359251
	mov DWORD PTR [eax+40], edx
	mov edx, 2091905
	mov DWORD PTR [eax+44], edx
	mov edx, 5260684
	mov DWORD PTR [eax+48], edx
	mov edx, 2884855
	mov DWORD PTR [eax+52], edx
	mov edx, 5268920
	mov DWORD PTR [eax+56], edx
	mov edx, 5700314
	mov DWORD PTR [eax+60], edx
	mov edx, 5654953
	mov DWORD PTR [eax+64], edx
	mov edx, 7356305
	mov DWORD PTR [eax+68], edx
	mov edx, 1079900
	mov DWORD PTR [eax+72], edx
	mov edx, 4794489
	mov DWORD PTR [eax+76], edx
	mov edx, 549488
	mov DWORD PTR [eax+80], edx
	mov edx, 1119584
	mov DWORD PTR [eax+84], edx
	mov edx, 5760665
	mov DWORD PTR [eax+88], edx
	mov edx, 2108549
	mov DWORD PTR [eax+92], edx
	mov edx, 2118186
	mov DWORD PTR [eax+96], edx
	mov edx, 3859737
	mov DWORD PTR [eax+100], edx
	mov edx, 1399561
	mov DWORD PTR [eax+104], edx
	mov edx, 3277672
	mov DWORD PTR [eax+108], edx
	mov edx, 6623180
	mov DWORD PTR [eax+112], edx
	mov edx, 19422
	mov DWORD PTR [eax+116], edx
	mov edx, 4369920
	mov DWORD PTR [eax+120], edx
	mov edx, 8100412
	mov DWORD PTR [eax+124], edx
	mov edx, 5674394
	mov DWORD PTR [eax+128], edx
	mov edx, 8284641
	mov DWORD PTR [eax+132], edx
	mov edx, 5303092
	mov DWORD PTR [eax+136], edx
	mov edx, 4849980
	mov DWORD PTR [eax+140], edx
	mov edx, 1661693
	mov DWORD PTR [eax+144], edx
	mov edx, 3592148
	mov DWORD PTR [eax+148], edx
	mov edx, 2537516
	mov DWORD PTR [eax+152], edx
	mov edx, 4464978
	mov DWORD PTR [eax+156], edx
	mov edx, 3861115
	mov DWORD PTR [eax+160], edx
	mov edx, 3043716
	mov DWORD PTR [eax+164], edx
	mov edx, 4805995
	mov DWORD PTR [eax+168], edx
	mov edx, 2867647
	mov DWORD PTR [eax+172], edx
	mov edx, 4840449
	mov DWORD PTR [eax+176], edx
	mov edx, 300467
	mov DWORD PTR [eax+180], edx
	mov edx, 6031717
	mov DWORD PTR [eax+184], edx
	mov edx, 539299
	mov DWORD PTR [eax+188], edx
	mov edx, 1699267
	mov DWORD PTR [eax+192], edx
	mov edx, 1643818
	mov DWORD PTR [eax+196], edx
	mov edx, 4874723
	mov DWORD PTR [eax+200], edx
	mov edx, 3821735
	mov DWORD PTR [eax+204], edx
	mov edx, 4873154
	mov DWORD PTR [eax+208], edx
	mov edx, 2140649
	mov DWORD PTR [eax+212], edx
	mov edx, 1600420
	mov DWORD PTR [eax+216], edx
	mov edx, 4680821
	mov DWORD PTR [eax+220], edx
	mov edx, 7568473
	mov DWORD PTR [eax+224], edx
	mov edx, 7849063
	mov DWORD PTR [eax+228], edx
	mov edx, 7426187
	mov DWORD PTR [eax+232], edx
	mov edx, 4499374
	mov DWORD PTR [eax+236], edx
	mov edx, 4479693
	mov DWORD PTR [eax+240], edx
	mov edx, 2556880
	mov DWORD PTR [eax+244], edx
	mov edx, 6308525
	mov DWORD PTR [eax+248], edx
	mov edx, 2797779
	mov DWORD PTR [eax+252], edx
	mov edx, 3930395
	mov DWORD PTR [eax+256], edx
	mov edx, 1528703
	mov DWORD PTR [eax+260], edx
	mov edx, 3677745
	mov DWORD PTR [eax+264], edx
	mov edx, 3041255
	mov DWORD PTR [eax+268], edx
	mov edx, 1452451
	mov DWORD PTR [eax+272], edx
	mov edx, 4904467
	mov DWORD PTR [eax+276], edx
	mov edx, 6203962
	mov DWORD PTR [eax+280], edx
	mov edx, 1585221
	mov DWORD PTR [eax+284], edx
	mov edx, 1257611
	mov DWORD PTR [eax+288], edx
	mov edx, 6441103
	mov DWORD PTR [eax+292], edx
	mov edx, 4083598
	mov DWORD PTR [eax+296], edx
	mov edx, 1000202
	mov DWORD PTR [eax+300], edx
	mov edx, 3190144
	mov DWORD PTR [eax+304], edx
	mov edx, 3157330
	mov DWORD PTR [eax+308], edx
	mov edx, 3632928
	mov DWORD PTR [eax+312], edx
	mov edx, 8253495
	mov DWORD PTR [eax+316], edx
	mov edx, 4968207
	mov DWORD PTR [eax+320], edx
	mov edx, 983419
	mov DWORD PTR [eax+324], edx
	mov edx, 6232521
	mov DWORD PTR [eax+328], edx
	mov edx, 5665122
	mov DWORD PTR [eax+332], edx
	mov edx, 2967645
	mov DWORD PTR [eax+336], edx
	mov edx, 3693493
	mov DWORD PTR [eax+340], edx
	mov edx, 411027
	mov DWORD PTR [eax+344], edx
	mov edx, 2477047
	mov DWORD PTR [eax+348], edx
	mov edx, 671102
	mov DWORD PTR [eax+352], edx
	mov edx, 1228525
	mov DWORD PTR [eax+356], edx
	mov edx, 22981
	mov DWORD PTR [eax+360], edx
	mov edx, 1308169
	mov DWORD PTR [eax+364], edx
	mov edx, 381987
	mov DWORD PTR [eax+368], edx
	mov edx, 7031341
	mov DWORD PTR [eax+372], edx
	mov edx, 6527646
	mov DWORD PTR [eax+376], edx
	mov edx, 1430430
	mov DWORD PTR [eax+380], edx
	mov edx, 3343383
	mov DWORD PTR [eax+384], edx
	mov edx, 8115473
	mov DWORD PTR [eax+388], edx
	mov edx, 7871466
	mov DWORD PTR [eax+392], edx
	mov edx, 5282425
	mov DWORD PTR [eax+396], edx
	mov edx, 8336129
	mov DWORD PTR [eax+400], edx
	mov edx, 1100098
	mov DWORD PTR [eax+404], edx
	mov edx, 7475901
	mov DWORD PTR [eax+408], edx
	mov edx, 4421799
	mov DWORD PTR [eax+412], edx
	mov edx, 3724342
	mov DWORD PTR [eax+416], edx
	mov edx, 8578
	mov DWORD PTR [eax+420], edx
	mov edx, 6727353
	mov DWORD PTR [eax+424], edx
	mov edx, 3249728
	mov DWORD PTR [eax+428], edx
	mov edx, 5991061
	mov DWORD PTR [eax+432], edx
	mov edx, 210977
	mov DWORD PTR [eax+436], edx
	mov edx, 7620448
	mov DWORD PTR [eax+440], edx
	mov edx, 1316856
	mov DWORD PTR [eax+444], edx
	mov edx, 8190869
	mov DWORD PTR [eax+448], edx
	mov edx, 3553272
	mov DWORD PTR [eax+452], edx
	mov edx, 5220671
	mov DWORD PTR [eax+456], edx
	mov edx, 1851402
	mov DWORD PTR [eax+460], edx
	mov edx, 2409325
	mov DWORD PTR [eax+464], edx
	mov edx, 177440
	mov DWORD PTR [eax+468], edx
	mov edx, 7064828
	mov DWORD PTR [eax+472], edx
	mov edx, 7039087
	mov DWORD PTR [eax+476], edx
	mov edx, 7094748
	mov DWORD PTR [eax+480], edx
	mov edx, 1584928
	mov DWORD PTR [eax+484], edx
	mov edx, 812732
	mov DWORD PTR [eax+488], edx
	mov edx, 1439742
	mov DWORD PTR [eax+492], edx
	mov edx, 3019102
	mov DWORD PTR [eax+496], edx
	mov edx, 3881060
	mov DWORD PTR [eax+500], edx
	mov edx, 3628969
	mov DWORD PTR [eax+504], edx
	mov edx, 4540456
	mov DWORD PTR [eax+508], edx
	mov edx, 6288750
	mov DWORD PTR [eax+512], edx
	mov edx, 4972711
	mov DWORD PTR [eax+516], edx
	mov edx, 6063917
	mov DWORD PTR [eax+520], edx
	mov edx, 4562441
	mov DWORD PTR [eax+524], edx
	mov edx, 3342478
	mov DWORD PTR [eax+528], edx
	mov edx, 6136326
	mov DWORD PTR [eax+532], edx
	mov edx, 2446433
	mov DWORD PTR [eax+536], edx
	mov edx, 3562462
	mov DWORD PTR [eax+540], edx
	mov edx, 8113420
	mov DWORD PTR [eax+544], edx
	mov edx, 5945978
	mov DWORD PTR [eax+548], edx
	mov edx, 1235728
	mov DWORD PTR [eax+552], edx
	mov edx, 4867236
	mov DWORD PTR [eax+556], edx
	mov edx, 3520352
	mov DWORD PTR [eax+560], edx
	mov edx, 3759364
	mov DWORD PTR [eax+564], edx
	mov edx, 1197226
	mov DWORD PTR [eax+568], edx
	mov edx, 3193378
	mov DWORD PTR [eax+572], edx
	mov edx, 7479715
	mov DWORD PTR [eax+576], edx
	mov edx, 6521319
	mov DWORD PTR [eax+580], edx
	mov edx, 7470875
	mov DWORD PTR [eax+584], edx
	mov edx, 7561383
	mov DWORD PTR [eax+588], edx
	mov edx, 7884926
	mov DWORD PTR [eax+592], edx
	mov edx, 1613174
	mov DWORD PTR [eax+596], edx
	mov edx, 43260
	mov DWORD PTR [eax+600], edx
	mov edx, 522500
	mov DWORD PTR [eax+604], edx
	mov edx, 655327
	mov DWORD PTR [eax+608], edx
	mov edx, 3122442
	mov DWORD PTR [eax+612], edx
	mov edx, 6348669
	mov DWORD PTR [eax+616], edx
	mov edx, 5173371
	mov DWORD PTR [eax+620], edx
	mov edx, 3556995
	mov DWORD PTR [eax+624], edx
	mov edx, 525098
	mov DWORD PTR [eax+628], edx
	mov edx, 768622
	mov DWORD PTR [eax+632], edx
	mov edx, 3595838
	mov DWORD PTR [eax+636], edx
	mov edx, 8038120
	mov DWORD PTR [eax+640], edx
	mov edx, 8093429
	mov DWORD PTR [eax+644], edx
	mov edx, 2437823
	mov DWORD PTR [eax+648], edx
	mov edx, 4272102
	mov DWORD PTR [eax+652], edx
	mov edx, 4943130
	mov DWORD PTR [eax+656], edx
	mov edx, 3342277
	mov DWORD PTR [eax+660], edx
	mov edx, 6644538
	mov DWORD PTR [eax+664], edx
	mov edx, 8177373
	mov DWORD PTR [eax+668], edx
	mov edx, 5538076
	mov DWORD PTR [eax+672], edx
	mov edx, 5688936
	mov DWORD PTR [eax+676], edx
	mov edx, 2590150
	mov DWORD PTR [eax+680], edx
	mov edx, 7115408
	mov DWORD PTR [eax+684], edx
	mov edx, 4325093
	mov DWORD PTR [eax+688], edx
	mov edx, 7132797
	mov DWORD PTR [eax+692], edx
	mov edx, 5894064
	mov DWORD PTR [eax+696], edx
	mov edx, 6784443
	mov DWORD PTR [eax+700], edx
	mov edx, 3767016
	mov DWORD PTR [eax+704], edx
	mov edx, 7129923
	mov DWORD PTR [eax+708], edx
	mov edx, 5744496
	mov DWORD PTR [eax+712], edx
	mov edx, 3548272
	mov DWORD PTR [eax+716], edx
	mov edx, 2994039
	mov DWORD PTR [eax+720], edx
	mov edx, 6511298
	mov DWORD PTR [eax+724], edx
	mov edx, 6476982
	mov DWORD PTR [eax+728], edx
	mov edx, 1050970
	mov DWORD PTR [eax+732], edx
	mov edx, 1333058
	mov DWORD PTR [eax+736], edx
	mov edx, 7143142
	mov DWORD PTR [eax+740], edx
	mov edx, 3318210
	mov DWORD PTR [eax+744], edx
	mov edx, 1430225
	mov DWORD PTR [eax+748], edx
	mov edx, 451100
	mov DWORD PTR [eax+752], edx
	mov edx, 7067962
	mov DWORD PTR [eax+756], edx
	mov edx, 5074302
	mov DWORD PTR [eax+760], edx
	mov edx, 1962642
	mov DWORD PTR [eax+764], edx
	mov edx, 1279661
	mov DWORD PTR [eax+768], edx
	mov edx, 6463336
	mov DWORD PTR [eax+772], edx
	mov edx, 2546312
	mov DWORD PTR [eax+776], edx
	mov edx, 1374803
	mov DWORD PTR [eax+780], edx
	mov edx, 6880252
	mov DWORD PTR [eax+784], edx
	mov edx, 7603226
	mov DWORD PTR [eax+788], edx
	mov edx, 6144537
	mov DWORD PTR [eax+792], edx
	mov edx, 4974386
	mov DWORD PTR [eax+796], edx
	mov edx, 542412
	mov DWORD PTR [eax+800], edx
	mov edx, 2831860
	mov DWORD PTR [eax+804], edx
	mov edx, 1671176
	mov DWORD PTR [eax+808], edx
	mov edx, 1846953
	mov DWORD PTR [eax+812], edx
	mov edx, 2584293
	mov DWORD PTR [eax+816], edx
	mov edx, 3724270
	mov DWORD PTR [eax+820], edx
	mov edx, 7786281
	mov DWORD PTR [eax+824], edx
	mov edx, 3776993
	mov DWORD PTR [eax+828], edx
	mov edx, 2013608
	mov DWORD PTR [eax+832], edx
	mov edx, 5948022
	mov DWORD PTR [eax+836], edx
	mov edx, 5925962
	mov DWORD PTR [eax+840], edx
	mov edx, 164721
	mov DWORD PTR [eax+844], edx
	mov edx, 6423145
	mov DWORD PTR [eax+848], edx
	mov edx, 5011305
	mov DWORD PTR [eax+852], edx
	mov edx, 8194886
	mov DWORD PTR [eax+856], edx
	mov edx, 1207385
	mov DWORD PTR [eax+860], edx
	mov edx, 3183426
	mov DWORD PTR [eax+864], edx
	mov edx, 8217573
	mov DWORD PTR [eax+868], edx
	mov edx, 6764025
	mov DWORD PTR [eax+872], edx
	mov edx, 5366416
	mov DWORD PTR [eax+876], edx
	mov edx, 7570268
	mov DWORD PTR [eax+880], edx
	mov edx, 6727783
	mov DWORD PTR [eax+884], edx
	mov edx, 3694233
	mov DWORD PTR [eax+888], edx
	mov edx, 1799107
	mov DWORD PTR [eax+892], edx
	mov edx, 3038916
	mov DWORD PTR [eax+896], edx
	mov edx, 4856520
	mov DWORD PTR [eax+900], edx
	mov edx, 4513516
	mov DWORD PTR [eax+904], edx
	mov edx, 8110657
	mov DWORD PTR [eax+908], edx
	mov edx, 6167306
	mov DWORD PTR [eax+912], edx
	mov edx, 975884
	mov DWORD PTR [eax+916], edx
	mov edx, 6662682
	mov DWORD PTR [eax+920], edx
	mov edx, 7908339
	mov DWORD PTR [eax+924], edx
	mov edx, 426683
	mov DWORD PTR [eax+928], edx
	mov edx, 6656817
	mov DWORD PTR [eax+932], edx
	mov edx, 1803090
	mov DWORD PTR [eax+936], edx
	mov edx, 6470041
	mov DWORD PTR [eax+940], edx
	mov edx, 1667432
	mov DWORD PTR [eax+944], edx
	mov edx, 1104333
	mov DWORD PTR [eax+948], edx
	mov edx, 260646
	mov DWORD PTR [eax+952], edx
	mov edx, 3833893
	mov DWORD PTR [eax+956], edx
	mov edx, 2939036
	mov DWORD PTR [eax+960], edx
	mov edx, 2235985
	mov DWORD PTR [eax+964], edx
	mov edx, 420899
	mov DWORD PTR [eax+968], edx
	mov edx, 2286327
	mov DWORD PTR [eax+972], edx
	mov edx, 8196974
	mov DWORD PTR [eax+976], edx
	mov edx, 976891
	mov DWORD PTR [eax+980], edx
	mov edx, 6767575
	mov DWORD PTR [eax+984], edx
	mov edx, 3545687
	mov DWORD PTR [eax+988], edx
	mov edx, 554416
	mov DWORD PTR [eax+992], edx
	mov edx, 4460757
	mov DWORD PTR [eax+996], edx
	mov edx, 48306
	mov DWORD PTR [eax+1000], edx
	mov edx, 1362209
	mov DWORD PTR [eax+1004], edx
	mov edx, 4442679
	mov DWORD PTR [eax+1008], edx
	mov edx, 6979993
	mov DWORD PTR [eax+1012], edx
	mov edx, 846154
	mov DWORD PTR [eax+1016], edx
	mov edx, 6403635
	mov DWORD PTR [eax+1020], edx
	mov ebp, eax
	add ebp, 1020
	mov edx, DWORD PTR [esp+20]
	add edx, 1024
	mov DWORD PTR [esp+24], edx
	mov esi, DWORD PTR [esp+20]
20:
	mov edi, esi
	add edi, 4
	mov ecx, 1
21:
	mov ebx, DWORD PTR [esi]
	add ebx, 8380417
	sub ebx, DWORD PTR [edi]
	mov eax, DWORD PTR [esi]
	add eax, DWORD PTR [edi]
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	mov eax, ebx
	mov edx, DWORD PTR [ebp]
	mul edx
	mov ebx, edx
	mov edx, -58728449
	mul edx
	mov edx, 8380417
	mul edx
	add eax, -1
	adc ebx, edx
	sub ebx, 8380417
	sbb edx, edx
	and edx, 8380417
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
	add edi, 8
	mov ecx, 2
23:
	mov ebx, DWORD PTR [esi]
	add ebx, 8380417
	sub ebx, DWORD PTR [edi]
	mov eax, DWORD PTR [esi]
	add eax, DWORD PTR [edi]
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	mov eax, ebx
	mov edx, DWORD PTR [ebp]
	mul edx
	mov ebx, edx
	mov edx, -58728449
	mul edx
	mov edx, 8380417
	mul edx
	add eax, -1
	adc ebx, edx
	sub ebx, 8380417
	sbb edx, edx
	and edx, 8380417
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
	add edi, 16
	mov ecx, 4
25:
	mov ebx, DWORD PTR [esi]
	add ebx, 8380417
	sub ebx, DWORD PTR [edi]
	mov eax, DWORD PTR [esi]
	add eax, DWORD PTR [edi]
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	mov eax, ebx
	mov edx, DWORD PTR [ebp]
	mul edx
	mov ebx, edx
	mov edx, -58728449
	mul edx
	mov edx, 8380417
	mul edx
	add eax, -1
	adc ebx, edx
	sub ebx, 8380417
	sbb edx, edx
	and edx, 8380417
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
	add edi, 32
	mov ecx, 8
27:
	mov ebx, DWORD PTR [esi]
	add ebx, 8380417
	sub ebx, DWORD PTR [edi]
	mov eax, DWORD PTR [esi]
	add eax, DWORD PTR [edi]
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	mov eax, ebx
	mov edx, DWORD PTR [ebp]
	mul edx
	mov ebx, edx
	mov edx, -58728449
	mul edx
	mov edx, 8380417
	mul edx
	add eax, -1
	adc ebx, edx
	sub ebx, 8380417
	sbb edx, edx
	and edx, 8380417
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
	add edi, 64
	mov ecx, 16
29:
	mov ebx, DWORD PTR [esi]
	add ebx, 8380417
	sub ebx, DWORD PTR [edi]
	mov eax, DWORD PTR [esi]
	add eax, DWORD PTR [edi]
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	mov eax, ebx
	mov edx, DWORD PTR [ebp]
	mul edx
	mov ebx, edx
	mov edx, -58728449
	mul edx
	mov edx, 8380417
	mul edx
	add eax, -1
	adc ebx, edx
	sub ebx, 8380417
	sbb edx, edx
	and edx, 8380417
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
	add edi, 128
	mov ecx, 32
211:
	mov ebx, DWORD PTR [esi]
	add ebx, 8380417
	sub ebx, DWORD PTR [edi]
	mov eax, DWORD PTR [esi]
	add eax, DWORD PTR [edi]
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	mov eax, ebx
	mov edx, DWORD PTR [ebp]
	mul edx
	mov ebx, edx
	mov edx, -58728449
	mul edx
	mov edx, 8380417
	mul edx
	add eax, -1
	adc ebx, edx
	sub ebx, 8380417
	sbb edx, edx
	and edx, 8380417
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
	add edi, 256
	mov ecx, 64
213:
	mov ebx, DWORD PTR [esi]
	add ebx, 8380417
	sub ebx, DWORD PTR [edi]
	mov eax, DWORD PTR [esi]
	add eax, DWORD PTR [edi]
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	mov eax, ebx
	mov edx, DWORD PTR [ebp]
	mul edx
	mov ebx, edx
	mov edx, -58728449
	mul edx
	mov edx, 8380417
	mul edx
	add eax, -1
	adc ebx, edx
	sub ebx, 8380417
	sbb edx, edx
	and edx, 8380417
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
214:
	mov edi, esi
	add edi, 512
	mov ecx, 128
215:
	mov ebx, DWORD PTR [esi]
	add ebx, 8380417
	sub ebx, DWORD PTR [edi]
	mov eax, DWORD PTR [esi]
	add eax, DWORD PTR [edi]
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	mov eax, ebx
	mov edx, DWORD PTR [ebp]
	mul edx
	mov ebx, edx
	mov edx, -58728449
	mul edx
	mov edx, 8380417
	mul edx
	add eax, -1
	adc ebx, edx
	sub ebx, 8380417
	sbb edx, edx
	and edx, 8380417
	add ebx, edx
	mov DWORD PTR [edi], ebx
	add esi, 4
	add edi, 4
	sub ecx, 1
	jne 215b
	mov esi, edi
	sub ebp, 4
	cmp esi, DWORD PTR [esp+24]
	jne 214b
	mov esi, DWORD PTR [esp+20]
	mov ecx, 256
216:
	mov eax, DWORD PTR [esi]
	mov edx, 16382
	mul edx
	mov ebx, edx
	mov edx, -58728449
	mul edx
	mov edx, 8380417
	mul edx
	add eax, -1
	adc ebx, edx
	sub ebx, 8380417
	sbb edx, edx
	and edx, 8380417
	add ebx, edx
	mov DWORD PTR [esi], ebx
	add esi, 4
	sub ecx, 1
	jne 216b
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
