// The functions of `src/internal/vg_mldsa_ntt.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_ntt:
	push ebx
	push esi
	push edi
	push ebp
	mov eax, DWORD PTR [esp+24]
	mov edx, 4193792
	mov DWORD PTR [eax], edx
	mov edx, 25847
	mov DWORD PTR [eax+4], edx
	mov edx, 5771523
	mov DWORD PTR [eax+8], edx
	mov edx, 7861508
	mov DWORD PTR [eax+12], edx
	mov edx, 237124
	mov DWORD PTR [eax+16], edx
	mov edx, 7602457
	mov DWORD PTR [eax+20], edx
	mov edx, 7504169
	mov DWORD PTR [eax+24], edx
	mov edx, 466468
	mov DWORD PTR [eax+28], edx
	mov edx, 1826347
	mov DWORD PTR [eax+32], edx
	mov edx, 2353451
	mov DWORD PTR [eax+36], edx
	mov edx, 8021166
	mov DWORD PTR [eax+40], edx
	mov edx, 6288512
	mov DWORD PTR [eax+44], edx
	mov edx, 3119733
	mov DWORD PTR [eax+48], edx
	mov edx, 5495562
	mov DWORD PTR [eax+52], edx
	mov edx, 3111497
	mov DWORD PTR [eax+56], edx
	mov edx, 2680103
	mov DWORD PTR [eax+60], edx
	mov edx, 2725464
	mov DWORD PTR [eax+64], edx
	mov edx, 1024112
	mov DWORD PTR [eax+68], edx
	mov edx, 7300517
	mov DWORD PTR [eax+72], edx
	mov edx, 3585928
	mov DWORD PTR [eax+76], edx
	mov edx, 7830929
	mov DWORD PTR [eax+80], edx
	mov edx, 7260833
	mov DWORD PTR [eax+84], edx
	mov edx, 2619752
	mov DWORD PTR [eax+88], edx
	mov edx, 6271868
	mov DWORD PTR [eax+92], edx
	mov edx, 6262231
	mov DWORD PTR [eax+96], edx
	mov edx, 4520680
	mov DWORD PTR [eax+100], edx
	mov edx, 6980856
	mov DWORD PTR [eax+104], edx
	mov edx, 5102745
	mov DWORD PTR [eax+108], edx
	mov edx, 1757237
	mov DWORD PTR [eax+112], edx
	mov edx, 8360995
	mov DWORD PTR [eax+116], edx
	mov edx, 4010497
	mov DWORD PTR [eax+120], edx
	mov edx, 280005
	mov DWORD PTR [eax+124], edx
	mov edx, 2706023
	mov DWORD PTR [eax+128], edx
	mov edx, 95776
	mov DWORD PTR [eax+132], edx
	mov edx, 3077325
	mov DWORD PTR [eax+136], edx
	mov edx, 3530437
	mov DWORD PTR [eax+140], edx
	mov edx, 6718724
	mov DWORD PTR [eax+144], edx
	mov edx, 4788269
	mov DWORD PTR [eax+148], edx
	mov edx, 5842901
	mov DWORD PTR [eax+152], edx
	mov edx, 3915439
	mov DWORD PTR [eax+156], edx
	mov edx, 4519302
	mov DWORD PTR [eax+160], edx
	mov edx, 5336701
	mov DWORD PTR [eax+164], edx
	mov edx, 3574422
	mov DWORD PTR [eax+168], edx
	mov edx, 5512770
	mov DWORD PTR [eax+172], edx
	mov edx, 3539968
	mov DWORD PTR [eax+176], edx
	mov edx, 8079950
	mov DWORD PTR [eax+180], edx
	mov edx, 2348700
	mov DWORD PTR [eax+184], edx
	mov edx, 7841118
	mov DWORD PTR [eax+188], edx
	mov edx, 6681150
	mov DWORD PTR [eax+192], edx
	mov edx, 6736599
	mov DWORD PTR [eax+196], edx
	mov edx, 3505694
	mov DWORD PTR [eax+200], edx
	mov edx, 4558682
	mov DWORD PTR [eax+204], edx
	mov edx, 3507263
	mov DWORD PTR [eax+208], edx
	mov edx, 6239768
	mov DWORD PTR [eax+212], edx
	mov edx, 6779997
	mov DWORD PTR [eax+216], edx
	mov edx, 3699596
	mov DWORD PTR [eax+220], edx
	mov edx, 811944
	mov DWORD PTR [eax+224], edx
	mov edx, 531354
	mov DWORD PTR [eax+228], edx
	mov edx, 954230
	mov DWORD PTR [eax+232], edx
	mov edx, 3881043
	mov DWORD PTR [eax+236], edx
	mov edx, 3900724
	mov DWORD PTR [eax+240], edx
	mov edx, 5823537
	mov DWORD PTR [eax+244], edx
	mov edx, 2071892
	mov DWORD PTR [eax+248], edx
	mov edx, 5582638
	mov DWORD PTR [eax+252], edx
	mov edx, 4450022
	mov DWORD PTR [eax+256], edx
	mov edx, 6851714
	mov DWORD PTR [eax+260], edx
	mov edx, 4702672
	mov DWORD PTR [eax+264], edx
	mov edx, 5339162
	mov DWORD PTR [eax+268], edx
	mov edx, 6927966
	mov DWORD PTR [eax+272], edx
	mov edx, 3475950
	mov DWORD PTR [eax+276], edx
	mov edx, 2176455
	mov DWORD PTR [eax+280], edx
	mov edx, 6795196
	mov DWORD PTR [eax+284], edx
	mov edx, 7122806
	mov DWORD PTR [eax+288], edx
	mov edx, 1939314
	mov DWORD PTR [eax+292], edx
	mov edx, 4296819
	mov DWORD PTR [eax+296], edx
	mov edx, 7380215
	mov DWORD PTR [eax+300], edx
	mov edx, 5190273
	mov DWORD PTR [eax+304], edx
	mov edx, 5223087
	mov DWORD PTR [eax+308], edx
	mov edx, 4747489
	mov DWORD PTR [eax+312], edx
	mov edx, 126922
	mov DWORD PTR [eax+316], edx
	mov edx, 3412210
	mov DWORD PTR [eax+320], edx
	mov edx, 7396998
	mov DWORD PTR [eax+324], edx
	mov edx, 2147896
	mov DWORD PTR [eax+328], edx
	mov edx, 2715295
	mov DWORD PTR [eax+332], edx
	mov edx, 5412772
	mov DWORD PTR [eax+336], edx
	mov edx, 4686924
	mov DWORD PTR [eax+340], edx
	mov edx, 7969390
	mov DWORD PTR [eax+344], edx
	mov edx, 5903370
	mov DWORD PTR [eax+348], edx
	mov edx, 7709315
	mov DWORD PTR [eax+352], edx
	mov edx, 7151892
	mov DWORD PTR [eax+356], edx
	mov edx, 8357436
	mov DWORD PTR [eax+360], edx
	mov edx, 7072248
	mov DWORD PTR [eax+364], edx
	mov edx, 7998430
	mov DWORD PTR [eax+368], edx
	mov edx, 1349076
	mov DWORD PTR [eax+372], edx
	mov edx, 1852771
	mov DWORD PTR [eax+376], edx
	mov edx, 6949987
	mov DWORD PTR [eax+380], edx
	mov edx, 5037034
	mov DWORD PTR [eax+384], edx
	mov edx, 264944
	mov DWORD PTR [eax+388], edx
	mov edx, 508951
	mov DWORD PTR [eax+392], edx
	mov edx, 3097992
	mov DWORD PTR [eax+396], edx
	mov edx, 44288
	mov DWORD PTR [eax+400], edx
	mov edx, 7280319
	mov DWORD PTR [eax+404], edx
	mov edx, 904516
	mov DWORD PTR [eax+408], edx
	mov edx, 3958618
	mov DWORD PTR [eax+412], edx
	mov edx, 4656075
	mov DWORD PTR [eax+416], edx
	mov edx, 8371839
	mov DWORD PTR [eax+420], edx
	mov edx, 1653064
	mov DWORD PTR [eax+424], edx
	mov edx, 5130689
	mov DWORD PTR [eax+428], edx
	mov edx, 2389356
	mov DWORD PTR [eax+432], edx
	mov edx, 8169440
	mov DWORD PTR [eax+436], edx
	mov edx, 759969
	mov DWORD PTR [eax+440], edx
	mov edx, 7063561
	mov DWORD PTR [eax+444], edx
	mov edx, 189548
	mov DWORD PTR [eax+448], edx
	mov edx, 4827145
	mov DWORD PTR [eax+452], edx
	mov edx, 3159746
	mov DWORD PTR [eax+456], edx
	mov edx, 6529015
	mov DWORD PTR [eax+460], edx
	mov edx, 5971092
	mov DWORD PTR [eax+464], edx
	mov edx, 8202977
	mov DWORD PTR [eax+468], edx
	mov edx, 1315589
	mov DWORD PTR [eax+472], edx
	mov edx, 1341330
	mov DWORD PTR [eax+476], edx
	mov edx, 1285669
	mov DWORD PTR [eax+480], edx
	mov edx, 6795489
	mov DWORD PTR [eax+484], edx
	mov edx, 7567685
	mov DWORD PTR [eax+488], edx
	mov edx, 6940675
	mov DWORD PTR [eax+492], edx
	mov edx, 5361315
	mov DWORD PTR [eax+496], edx
	mov edx, 4499357
	mov DWORD PTR [eax+500], edx
	mov edx, 4751448
	mov DWORD PTR [eax+504], edx
	mov edx, 3839961
	mov DWORD PTR [eax+508], edx
	mov edx, 2091667
	mov DWORD PTR [eax+512], edx
	mov edx, 3407706
	mov DWORD PTR [eax+516], edx
	mov edx, 2316500
	mov DWORD PTR [eax+520], edx
	mov edx, 3817976
	mov DWORD PTR [eax+524], edx
	mov edx, 5037939
	mov DWORD PTR [eax+528], edx
	mov edx, 2244091
	mov DWORD PTR [eax+532], edx
	mov edx, 5933984
	mov DWORD PTR [eax+536], edx
	mov edx, 4817955
	mov DWORD PTR [eax+540], edx
	mov edx, 266997
	mov DWORD PTR [eax+544], edx
	mov edx, 2434439
	mov DWORD PTR [eax+548], edx
	mov edx, 7144689
	mov DWORD PTR [eax+552], edx
	mov edx, 3513181
	mov DWORD PTR [eax+556], edx
	mov edx, 4860065
	mov DWORD PTR [eax+560], edx
	mov edx, 4621053
	mov DWORD PTR [eax+564], edx
	mov edx, 7183191
	mov DWORD PTR [eax+568], edx
	mov edx, 5187039
	mov DWORD PTR [eax+572], edx
	mov edx, 900702
	mov DWORD PTR [eax+576], edx
	mov edx, 1859098
	mov DWORD PTR [eax+580], edx
	mov edx, 909542
	mov DWORD PTR [eax+584], edx
	mov edx, 819034
	mov DWORD PTR [eax+588], edx
	mov edx, 495491
	mov DWORD PTR [eax+592], edx
	mov edx, 6767243
	mov DWORD PTR [eax+596], edx
	mov edx, 8337157
	mov DWORD PTR [eax+600], edx
	mov edx, 7857917
	mov DWORD PTR [eax+604], edx
	mov edx, 7725090
	mov DWORD PTR [eax+608], edx
	mov edx, 5257975
	mov DWORD PTR [eax+612], edx
	mov edx, 2031748
	mov DWORD PTR [eax+616], edx
	mov edx, 3207046
	mov DWORD PTR [eax+620], edx
	mov edx, 4823422
	mov DWORD PTR [eax+624], edx
	mov edx, 7855319
	mov DWORD PTR [eax+628], edx
	mov edx, 7611795
	mov DWORD PTR [eax+632], edx
	mov edx, 4784579
	mov DWORD PTR [eax+636], edx
	mov edx, 342297
	mov DWORD PTR [eax+640], edx
	mov edx, 286988
	mov DWORD PTR [eax+644], edx
	mov edx, 5942594
	mov DWORD PTR [eax+648], edx
	mov edx, 4108315
	mov DWORD PTR [eax+652], edx
	mov edx, 3437287
	mov DWORD PTR [eax+656], edx
	mov edx, 5038140
	mov DWORD PTR [eax+660], edx
	mov edx, 1735879
	mov DWORD PTR [eax+664], edx
	mov edx, 203044
	mov DWORD PTR [eax+668], edx
	mov edx, 2842341
	mov DWORD PTR [eax+672], edx
	mov edx, 2691481
	mov DWORD PTR [eax+676], edx
	mov edx, 5790267
	mov DWORD PTR [eax+680], edx
	mov edx, 1265009
	mov DWORD PTR [eax+684], edx
	mov edx, 4055324
	mov DWORD PTR [eax+688], edx
	mov edx, 1247620
	mov DWORD PTR [eax+692], edx
	mov edx, 2486353
	mov DWORD PTR [eax+696], edx
	mov edx, 1595974
	mov DWORD PTR [eax+700], edx
	mov edx, 4613401
	mov DWORD PTR [eax+704], edx
	mov edx, 1250494
	mov DWORD PTR [eax+708], edx
	mov edx, 2635921
	mov DWORD PTR [eax+712], edx
	mov edx, 4832145
	mov DWORD PTR [eax+716], edx
	mov edx, 5386378
	mov DWORD PTR [eax+720], edx
	mov edx, 1869119
	mov DWORD PTR [eax+724], edx
	mov edx, 1903435
	mov DWORD PTR [eax+728], edx
	mov edx, 7329447
	mov DWORD PTR [eax+732], edx
	mov edx, 7047359
	mov DWORD PTR [eax+736], edx
	mov edx, 1237275
	mov DWORD PTR [eax+740], edx
	mov edx, 5062207
	mov DWORD PTR [eax+744], edx
	mov edx, 6950192
	mov DWORD PTR [eax+748], edx
	mov edx, 7929317
	mov DWORD PTR [eax+752], edx
	mov edx, 1312455
	mov DWORD PTR [eax+756], edx
	mov edx, 3306115
	mov DWORD PTR [eax+760], edx
	mov edx, 6417775
	mov DWORD PTR [eax+764], edx
	mov edx, 7100756
	mov DWORD PTR [eax+768], edx
	mov edx, 1917081
	mov DWORD PTR [eax+772], edx
	mov edx, 5834105
	mov DWORD PTR [eax+776], edx
	mov edx, 7005614
	mov DWORD PTR [eax+780], edx
	mov edx, 1500165
	mov DWORD PTR [eax+784], edx
	mov edx, 777191
	mov DWORD PTR [eax+788], edx
	mov edx, 2235880
	mov DWORD PTR [eax+792], edx
	mov edx, 3406031
	mov DWORD PTR [eax+796], edx
	mov edx, 7838005
	mov DWORD PTR [eax+800], edx
	mov edx, 5548557
	mov DWORD PTR [eax+804], edx
	mov edx, 6709241
	mov DWORD PTR [eax+808], edx
	mov edx, 6533464
	mov DWORD PTR [eax+812], edx
	mov edx, 5796124
	mov DWORD PTR [eax+816], edx
	mov edx, 4656147
	mov DWORD PTR [eax+820], edx
	mov edx, 594136
	mov DWORD PTR [eax+824], edx
	mov edx, 4603424
	mov DWORD PTR [eax+828], edx
	mov edx, 6366809
	mov DWORD PTR [eax+832], edx
	mov edx, 2432395
	mov DWORD PTR [eax+836], edx
	mov edx, 2454455
	mov DWORD PTR [eax+840], edx
	mov edx, 8215696
	mov DWORD PTR [eax+844], edx
	mov edx, 1957272
	mov DWORD PTR [eax+848], edx
	mov edx, 3369112
	mov DWORD PTR [eax+852], edx
	mov edx, 185531
	mov DWORD PTR [eax+856], edx
	mov edx, 7173032
	mov DWORD PTR [eax+860], edx
	mov edx, 5196991
	mov DWORD PTR [eax+864], edx
	mov edx, 162844
	mov DWORD PTR [eax+868], edx
	mov edx, 1616392
	mov DWORD PTR [eax+872], edx
	mov edx, 3014001
	mov DWORD PTR [eax+876], edx
	mov edx, 810149
	mov DWORD PTR [eax+880], edx
	mov edx, 1652634
	mov DWORD PTR [eax+884], edx
	mov edx, 4686184
	mov DWORD PTR [eax+888], edx
	mov edx, 6581310
	mov DWORD PTR [eax+892], edx
	mov edx, 5341501
	mov DWORD PTR [eax+896], edx
	mov edx, 3523897
	mov DWORD PTR [eax+900], edx
	mov edx, 3866901
	mov DWORD PTR [eax+904], edx
	mov edx, 269760
	mov DWORD PTR [eax+908], edx
	mov edx, 2213111
	mov DWORD PTR [eax+912], edx
	mov edx, 7404533
	mov DWORD PTR [eax+916], edx
	mov edx, 1717735
	mov DWORD PTR [eax+920], edx
	mov edx, 472078
	mov DWORD PTR [eax+924], edx
	mov edx, 7953734
	mov DWORD PTR [eax+928], edx
	mov edx, 1723600
	mov DWORD PTR [eax+932], edx
	mov edx, 6577327
	mov DWORD PTR [eax+936], edx
	mov edx, 1910376
	mov DWORD PTR [eax+940], edx
	mov edx, 6712985
	mov DWORD PTR [eax+944], edx
	mov edx, 7276084
	mov DWORD PTR [eax+948], edx
	mov edx, 8119771
	mov DWORD PTR [eax+952], edx
	mov edx, 4546524
	mov DWORD PTR [eax+956], edx
	mov edx, 5441381
	mov DWORD PTR [eax+960], edx
	mov edx, 6144432
	mov DWORD PTR [eax+964], edx
	mov edx, 7959518
	mov DWORD PTR [eax+968], edx
	mov edx, 6094090
	mov DWORD PTR [eax+972], edx
	mov edx, 183443
	mov DWORD PTR [eax+976], edx
	mov edx, 7403526
	mov DWORD PTR [eax+980], edx
	mov edx, 1612842
	mov DWORD PTR [eax+984], edx
	mov edx, 4834730
	mov DWORD PTR [eax+988], edx
	mov edx, 7826001
	mov DWORD PTR [eax+992], edx
	mov edx, 3919660
	mov DWORD PTR [eax+996], edx
	mov edx, 8332111
	mov DWORD PTR [eax+1000], edx
	mov edx, 7018208
	mov DWORD PTR [eax+1004], edx
	mov edx, 3937738
	mov DWORD PTR [eax+1008], edx
	mov edx, 1400424
	mov DWORD PTR [eax+1012], edx
	mov edx, 7534263
	mov DWORD PTR [eax+1016], edx
	mov edx, 1976782
	mov DWORD PTR [eax+1020], edx
	mov ebp, eax
	add ebp, 4
	mov edx, DWORD PTR [esp+20]
	add edx, 1024
	mov DWORD PTR [esp+24], edx
	mov esi, DWORD PTR [esp+20]
20:
	mov edi, esi
	add edi, 512
	mov ecx, 128
21:
	mov eax, DWORD PTR [edi]
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
	mov eax, DWORD PTR [esi]
	add eax, 8380417
	sub eax, ebx
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [esi]
	add eax, ebx
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	add esi, 4
	add edi, 4
	sub ecx, 1
	jne 21b
	mov esi, edi
	add ebp, 4
	cmp esi, DWORD PTR [esp+24]
	jne 20b
	mov esi, DWORD PTR [esp+20]
22:
	mov edi, esi
	add edi, 256
	mov ecx, 64
23:
	mov eax, DWORD PTR [edi]
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
	mov eax, DWORD PTR [esi]
	add eax, 8380417
	sub eax, ebx
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [esi]
	add eax, ebx
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	add esi, 4
	add edi, 4
	sub ecx, 1
	jne 23b
	mov esi, edi
	add ebp, 4
	cmp esi, DWORD PTR [esp+24]
	jne 22b
	mov esi, DWORD PTR [esp+20]
24:
	mov edi, esi
	add edi, 128
	mov ecx, 32
25:
	mov eax, DWORD PTR [edi]
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
	mov eax, DWORD PTR [esi]
	add eax, 8380417
	sub eax, ebx
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [esi]
	add eax, ebx
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	add esi, 4
	add edi, 4
	sub ecx, 1
	jne 25b
	mov esi, edi
	add ebp, 4
	cmp esi, DWORD PTR [esp+24]
	jne 24b
	mov esi, DWORD PTR [esp+20]
26:
	mov edi, esi
	add edi, 64
	mov ecx, 16
27:
	mov eax, DWORD PTR [edi]
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
	mov eax, DWORD PTR [esi]
	add eax, 8380417
	sub eax, ebx
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [esi]
	add eax, ebx
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	add esi, 4
	add edi, 4
	sub ecx, 1
	jne 27b
	mov esi, edi
	add ebp, 4
	cmp esi, DWORD PTR [esp+24]
	jne 26b
	mov esi, DWORD PTR [esp+20]
28:
	mov edi, esi
	add edi, 32
	mov ecx, 8
29:
	mov eax, DWORD PTR [edi]
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
	mov eax, DWORD PTR [esi]
	add eax, 8380417
	sub eax, ebx
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [esi]
	add eax, ebx
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	add esi, 4
	add edi, 4
	sub ecx, 1
	jne 29b
	mov esi, edi
	add ebp, 4
	cmp esi, DWORD PTR [esp+24]
	jne 28b
	mov esi, DWORD PTR [esp+20]
210:
	mov edi, esi
	add edi, 16
	mov ecx, 4
211:
	mov eax, DWORD PTR [edi]
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
	mov eax, DWORD PTR [esi]
	add eax, 8380417
	sub eax, ebx
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [esi]
	add eax, ebx
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	add esi, 4
	add edi, 4
	sub ecx, 1
	jne 211b
	mov esi, edi
	add ebp, 4
	cmp esi, DWORD PTR [esp+24]
	jne 210b
	mov esi, DWORD PTR [esp+20]
212:
	mov edi, esi
	add edi, 8
	mov ecx, 2
213:
	mov eax, DWORD PTR [edi]
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
	mov eax, DWORD PTR [esi]
	add eax, 8380417
	sub eax, ebx
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [esi]
	add eax, ebx
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	add esi, 4
	add edi, 4
	sub ecx, 1
	jne 213b
	mov esi, edi
	add ebp, 4
	cmp esi, DWORD PTR [esp+24]
	jne 212b
	mov esi, DWORD PTR [esp+20]
214:
	mov edi, esi
	add edi, 4
	mov ecx, 1
215:
	mov eax, DWORD PTR [edi]
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
	mov eax, DWORD PTR [esi]
	add eax, 8380417
	sub eax, ebx
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [esi]
	add eax, ebx
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	add esi, 4
	add edi, 4
	sub ecx, 1
	jne 215b
	mov esi, edi
	add ebp, 4
	cmp esi, DWORD PTR [esp+24]
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
