// The functions of `src/ecdh_p521.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdh_p521:
	mov r8, rcx
	mov r9, rdx
	mov rcx, rsi
	add rdx, 1
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r14, rdi
	mov rdi, r8
	mov rax, QWORD PTR [rcx+58]
	bswap rax
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rcx+50]
	bswap rax
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rcx+42]
	bswap rax
	mov QWORD PTR [rdi+2312], rax
	mov rax, QWORD PTR [rcx+34]
	bswap rax
	mov QWORD PTR [rdi+2320], rax
	mov rax, QWORD PTR [rcx+26]
	bswap rax
	mov QWORD PTR [rdi+2328], rax
	mov rax, QWORD PTR [rcx+18]
	bswap rax
	mov QWORD PTR [rdi+2336], rax
	mov rax, QWORD PTR [rcx+10]
	bswap rax
	mov QWORD PTR [rdi+2344], rax
	mov rax, QWORD PTR [rcx+2]
	bswap rax
	mov QWORD PTR [rdi+2352], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2360], rax
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2368], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2376], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2384], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2392], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2400], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2408], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2416], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2424], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2432], rax
	mov rax, QWORD PTR [rdx+58]
	bswap rax
	mov QWORD PTR [rdi+2440], rax
	mov rax, QWORD PTR [rdx+50]
	bswap rax
	mov QWORD PTR [rdi+2448], rax
	mov rax, QWORD PTR [rdx+42]
	bswap rax
	mov QWORD PTR [rdi+2456], rax
	mov rax, QWORD PTR [rdx+34]
	bswap rax
	mov QWORD PTR [rdi+2464], rax
	mov rax, QWORD PTR [rdx+26]
	bswap rax
	mov QWORD PTR [rdi+2472], rax
	mov rax, QWORD PTR [rdx+18]
	bswap rax
	mov QWORD PTR [rdi+2480], rax
	mov rax, QWORD PTR [rdx+10]
	bswap rax
	mov QWORD PTR [rdi+2488], rax
	mov rax, QWORD PTR [rdx+2]
	bswap rax
	mov QWORD PTR [rdi+2496], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2504], rax
	movabs rax, -1
	mov QWORD PTR [rdi+64], rax
	movabs rax, -1
	mov QWORD PTR [rdi+72], rax
	movabs rax, -1
	mov QWORD PTR [rdi+80], rax
	movabs rax, -1
	mov QWORD PTR [rdi+88], rax
	movabs rax, -1
	mov QWORD PTR [rdi+96], rax
	movabs rax, -1
	mov QWORD PTR [rdi+104], rax
	movabs rax, -1
	mov QWORD PTR [rdi+112], rax
	movabs rax, -1
	mov QWORD PTR [rdi+120], rax
	movabs rax, 511
	mov QWORD PTR [rdi+128], rax
	movabs rax, -4940528924288850935
	mov QWORD PTR [rdi+136], rax
	movabs rax, 4302566813442262958
	mov QWORD PTR [rdi+144], rax
	movabs rax, 9208736750959699408
	mov QWORD PTR [rdi+152], rax
	movabs rax, 5874531763869423211
	mov QWORD PTR [rdi+160], rax
	movabs rax, -6
	mov QWORD PTR [rdi+168], rax
	movabs rax, -1
	mov QWORD PTR [rdi+176], rax
	movabs rax, -1
	mov QWORD PTR [rdi+184], rax
	movabs rax, -1
	mov QWORD PTR [rdi+192], rax
	movabs rax, 511
	mov QWORD PTR [rdi+200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+280], rax
	movabs rax, 0
	mov QWORD PTR [rdi+288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+296], rax
	movabs rax, 0
	mov QWORD PTR [rdi+304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+344], rax
	movabs rax, 1
	mov QWORD PTR [rdi+352], rax
	movabs rax, 0
	mov QWORD PTR [rdi+360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+416], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+488], rax
	movabs rax, -108086391056891905
	mov QWORD PTR [rdi+496], rax
	movabs rax, -1
	mov QWORD PTR [rdi+504], rax
	movabs rax, -1
	mov QWORD PTR [rdi+512], rax
	movabs rax, -1
	mov QWORD PTR [rdi+520], rax
	movabs rax, -1
	mov QWORD PTR [rdi+528], rax
	movabs rax, -1
	mov QWORD PTR [rdi+536], rax
	movabs rax, -1
	mov QWORD PTR [rdi+544], rax
	movabs rax, -1
	mov QWORD PTR [rdi+552], rax
	movabs rax, 511
	mov QWORD PTR [rdi+560], rax
	movabs rax, -9206149359546586475
	mov QWORD PTR [rdi+568], rax
	movabs rax, 7703098954667325534
	mov QWORD PTR [rdi+576], rax
	movabs rax, -8444198932957117873
	mov QWORD PTR [rdi+584], rax
	movabs rax, 4080679219017386654
	mov QWORD PTR [rdi+592], rax
	movabs rax, -3314326249800548899
	mov QWORD PTR [rdi+600], rax
	movabs rax, -1327138235749078642
	mov QWORD PTR [rdi+608], rax
	movabs rax, 7346575694218300576
	mov QWORD PTR [rdi+616], rax
	movabs rax, 3412575346494654433
	mov QWORD PTR [rdi+624], rax
	movabs rax, 231
	mov QWORD PTR [rdi+632], rax
	movabs rax, -5534465018312146687
	mov QWORD PTR [rdi+640], rax
	movabs rax, 5619576712772809438
	mov QWORD PTR [rdi+648], rax
	movabs rax, 8005610518557668641
	mov QWORD PTR [rdi+656], rax
	movabs rax, -7746456476338520108
	mov QWORD PTR [rdi+664], rax
	movabs rax, -2499315621146659924
	mov QWORD PTR [rdi+672], rax
	movabs rax, -7999496471265827170
	mov QWORD PTR [rdi+680], rax
	movabs rax, 2399910904520155098
	mov QWORD PTR [rdi+688], rax
	movabs rax, -1815197603150574886
	mov QWORD PTR [rdi+696], rax
	movabs rax, 116
	mov QWORD PTR [rdi+704], rax
	movabs rax, 2902022722397546126
	mov QWORD PTR [rdi+712], rax
	movabs rax, 2325088080057329843
	mov QWORD PTR [rdi+720], rax
	movabs rax, -5721086412136040095
	mov QWORD PTR [rdi+728], rax
	movabs rax, 2333612672179754627
	mov QWORD PTR [rdi+736], rax
	movabs rax, 1606649517559478803
	mov QWORD PTR [rdi+744], rax
	movabs rax, 3750328465540489011
	mov QWORD PTR [rdi+752], rax
	movabs rax, -1383596148691055198
	mov QWORD PTR [rdi+760], rax
	movabs rax, 157139108829216397
	mov QWORD PTR [rdi+768], rax
	movabs rax, 480
	mov QWORD PTR [rdi+776], rax
	movabs rax, 1404226216438127876
	mov QWORD PTR [rdi+784], rax
	movabs rax, -646342563601285469
	mov QWORD PTR [rdi+792], rax
	movabs rax, 1344198287485662207
	mov QWORD PTR [rdi+800], rax
	movabs rax, -3210469545270092282
	mov QWORD PTR [rdi+808], rax
	movabs rax, -2491014132492810277
	mov QWORD PTR [rdi+816], rax
	movabs rax, -3462193604041806274
	mov QWORD PTR [rdi+824], rax
	movabs rax, 6614782218913277884
	mov QWORD PTR [rdi+832], rax
	movabs rax, 3282565375810407749
	mov QWORD PTR [rdi+840], rax
	movabs rax, 61
	mov QWORD PTR [rdi+848], rax
	movabs rax, -324259173170675712
	mov QWORD PTR [rdi+856], rax
	movabs rax, 2927982029091333069
	mov QWORD PTR [rdi+864], rax
	movabs rax, 1720978806102766044
	mov QWORD PTR [rdi+872], rax
	movabs rax, -3873067094995862739
	mov QWORD PTR [rdi+880], rax
	movabs rax, 204699087262476340
	mov QWORD PTR [rdi+888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+896], rax
	movabs rax, 0
	mov QWORD PTR [rdi+904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+920], rax
	movabs rax, -3
	mov QWORD PTR [rdi+928], rax
	movabs rax, -1
	mov QWORD PTR [rdi+936], rax
	movabs rax, -1
	mov QWORD PTR [rdi+944], rax
	movabs rax, -1
	mov QWORD PTR [rdi+952], rax
	movabs rax, -1
	mov QWORD PTR [rdi+960], rax
	movabs rax, -1
	mov QWORD PTR [rdi+968], rax
	movabs rax, -1
	mov QWORD PTR [rdi+976], rax
	movabs rax, -1
	mov QWORD PTR [rdi+984], rax
	movabs rax, 511
	mov QWORD PTR [rdi+992], rax
	movabs rax, -4940528924288850937
	mov QWORD PTR [rdi+1000], rax
	movabs rax, 4302566813442262958
	mov QWORD PTR [rdi+1008], rax
	movabs rax, 9208736750959699408
	mov QWORD PTR [rdi+1016], rax
	movabs rax, 5874531763869423211
	mov QWORD PTR [rdi+1024], rax
	movabs rax, -6
	mov QWORD PTR [rdi+1032], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1040], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1048], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1056], rax
	movabs rax, 511
	mov QWORD PTR [rdi+1064], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1080], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1088], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1104], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1112], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1184], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1248], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1280], rax
	movabs rax, -1
	mov QWORD PTR [rdi+3232], rax
	mov rsi, r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+2296]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3304], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3305], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3306], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3307], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3308], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3309], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3310], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3311], dl
	add rbx, 1
	cmp rbx, 72
	jne 20b
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rdi+rbx*1+928]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3888], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3889], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3890], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3891], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3892], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3893], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3894], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3895], dl
	add rbx, 1
	cmp rbx, 72
	jne 21b
	mov ebx, 0
22:
	movzx eax, BYTE PTR [rdi+rbx*1+1000]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4472], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4473], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4474], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4475], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4476], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4477], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4478], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4479], dl
	add rbx, 1
	cmp rbx, 72
	jne 22b
	movabs rax, 0
	mov QWORD PTR [rdi+2872], rax
	movabs rax, 70368744177664
	mov QWORD PTR [rdi+2880], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2896], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2920], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2928], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2936], rax
	movabs rax, -9217631144418712697
	mov QWORD PTR [rdi+2944], rax
	movabs rax, 8716614342792292383
	mov QWORD PTR [rdi+2952], rax
	movabs rax, -8963647668888889830
	mov QWORD PTR [rdi+2960], rax
	movabs rax, -4788688284897388321
	mov QWORD PTR [rdi+2968], rax
	movabs rax, -1104775416600182967
	mov QWORD PTR [rdi+2976], rax
	movabs rax, -442379411916359548
	mov QWORD PTR [rdi+2984], rax
	movabs rax, 8597773255975950730
	mov QWORD PTR [rdi+2992], rax
	movabs rax, 1137525115498218144
	mov QWORD PTR [rdi+3000], rax
	movabs rax, 77
	mov QWORD PTR [rdi+3008], rax
	mov rdx, r9
	add rdx, 67
	mov rax, QWORD PTR [rdx+58]
	bswap rax
	mov QWORD PTR [rdi+2656], rax
	mov rax, QWORD PTR [rdx+50]
	bswap rax
	mov QWORD PTR [rdi+2664], rax
	mov rax, QWORD PTR [rdx+42]
	bswap rax
	mov QWORD PTR [rdi+2672], rax
	mov rax, QWORD PTR [rdx+34]
	bswap rax
	mov QWORD PTR [rdi+2680], rax
	mov rax, QWORD PTR [rdx+26]
	bswap rax
	mov QWORD PTR [rdi+2688], rax
	mov rax, QWORD PTR [rdx+18]
	bswap rax
	mov QWORD PTR [rdi+2696], rax
	mov rax, QWORD PTR [rdx+10]
	bswap rax
	mov QWORD PTR [rdi+2704], rax
	mov rax, QWORD PTR [rdx+2]
	bswap rax
	mov QWORD PTR [rdi+2712], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2720], rax
	movzx edx, BYTE PTR [r9]
	xor rdx, 4
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	call {vg_p521_check_point}
	mov r8, QWORD PTR [rdi+2360]
	and r8, 511
	mov QWORD PTR [rdi+2360], r8
	movabs rax, -8608480567731124088
	mov QWORD PTR [rdi+5176], rax
	movabs rax, -8608480567731124088
	mov QWORD PTR [rdi+5184], rax
	movabs rax, -8608480567731124088
	mov QWORD PTR [rdi+5192], rax
	movabs rax, -8608480567731124088
	mov QWORD PTR [rdi+5200], rax
	movabs rax, -8608480567731124088
	mov QWORD PTR [rdi+5208], rax
	movabs rax, -8608480567731124088
	mov QWORD PTR [rdi+5216], rax
	movabs rax, -8608480567731124088
	mov QWORD PTR [rdi+5224], rax
	movabs rax, -8608480567731124088
	mov QWORD PTR [rdi+5232], rax
	movabs rax, 2184
	mov QWORD PTR [rdi+5240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5248], rax
	mov r8, QWORD PTR [rdi+5176]
	add r8, QWORD PTR [rdi+2296]
	mov QWORD PTR [rdi+5176], r8
	mov r8, QWORD PTR [rdi+5184]
	adc r8, QWORD PTR [rdi+2304]
	mov QWORD PTR [rdi+5184], r8
	mov r8, QWORD PTR [rdi+5192]
	adc r8, QWORD PTR [rdi+2312]
	mov QWORD PTR [rdi+5192], r8
	mov r8, QWORD PTR [rdi+5200]
	adc r8, QWORD PTR [rdi+2320]
	mov QWORD PTR [rdi+5200], r8
	mov r8, QWORD PTR [rdi+5208]
	adc r8, QWORD PTR [rdi+2328]
	mov QWORD PTR [rdi+5208], r8
	mov r8, QWORD PTR [rdi+5216]
	adc r8, QWORD PTR [rdi+2336]
	mov QWORD PTR [rdi+5216], r8
	mov r8, QWORD PTR [rdi+5224]
	adc r8, QWORD PTR [rdi+2344]
	mov QWORD PTR [rdi+5224], r8
	mov r8, QWORD PTR [rdi+5232]
	adc r8, QWORD PTR [rdi+2352]
	mov QWORD PTR [rdi+5232], r8
	mov r8, QWORD PTR [rdi+5240]
	adc r8, QWORD PTR [rdi+2360]
	mov QWORD PTR [rdi+5240], r8
	mov r8, QWORD PTR [rdi+5248]
	adc r8, 0
	mov QWORD PTR [rdi+5248], r8
	mov ebx, 0
23:
	movzx eax, BYTE PTR [rdi+rbx*1+5176]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+5320], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+5321], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+5322], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+5323], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+5324], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+5325], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+5326], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+5327], dl
	add rbx, 1
	cmp rbx, 80
	jne 23b
	mov rax, QWORD PTR [rdi+2800]
	mov QWORD PTR [rdi+6112], rax
	mov rax, QWORD PTR [rdi+2808]
	mov QWORD PTR [rdi+6120], rax
	mov rax, QWORD PTR [rdi+2816]
	mov QWORD PTR [rdi+6128], rax
	mov rax, QWORD PTR [rdi+2824]
	mov QWORD PTR [rdi+6136], rax
	mov rax, QWORD PTR [rdi+2832]
	mov QWORD PTR [rdi+6144], rax
	mov rax, QWORD PTR [rdi+2840]
	mov QWORD PTR [rdi+6152], rax
	mov rax, QWORD PTR [rdi+2848]
	mov QWORD PTR [rdi+6160], rax
	mov rax, QWORD PTR [rdi+2856]
	mov QWORD PTR [rdi+6168], rax
	mov rax, QWORD PTR [rdi+2864]
	mov QWORD PTR [rdi+6176], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+6184], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+6192], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+6200], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+6208], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+6216], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+6224], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+6232], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+6240], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+6248], rax
	mov rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+6256], rax
	mov rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+6264], rax
	mov rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+6272], rax
	mov rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+6280], rax
	mov rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+6288], rax
	mov rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+6296], rax
	mov rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+6304], rax
	mov rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+6312], rax
	mov rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+6320], rax
	mov rax, QWORD PTR [rdi+2800]
	mov QWORD PTR [rdi+1504], rax
	mov rax, QWORD PTR [rdi+2808]
	mov QWORD PTR [rdi+1512], rax
	mov rax, QWORD PTR [rdi+2816]
	mov QWORD PTR [rdi+1520], rax
	mov rax, QWORD PTR [rdi+2824]
	mov QWORD PTR [rdi+1528], rax
	mov rax, QWORD PTR [rdi+2832]
	mov QWORD PTR [rdi+1536], rax
	mov rax, QWORD PTR [rdi+2840]
	mov QWORD PTR [rdi+1544], rax
	mov rax, QWORD PTR [rdi+2848]
	mov QWORD PTR [rdi+1552], rax
	mov rax, QWORD PTR [rdi+2856]
	mov QWORD PTR [rdi+1560], rax
	mov rax, QWORD PTR [rdi+2864]
	mov QWORD PTR [rdi+1568], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+1600], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+1608], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+1616], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+1624], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+1632], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+1640], rax
	mov rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+1648], rax
	mov rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+1656], rax
	mov rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+1664], rax
	mov rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+1672], rax
	mov rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+1680], rax
	mov rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+1688], rax
	mov rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+1696], rax
	mov rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+1704], rax
	mov rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+1712], rax
	mov ebx, 7
24:
	sub rbx, 1
	mov r12, rsi
	mov esi, 1720
	mov edx, 1504
	mov ecx, 2800
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1576
	mov ecx, 3160
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1648
	mov ecx, 424
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1504
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 2800
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -1152
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 2008
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1576
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	add rdi, 3160
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -2736
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 864
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 2008
	mov edx, 2008
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 2008
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -720
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 720
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	add rdi, 1504
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 2800
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -2376
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 936
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1288
	mov edx, 1288
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1432
	mov edx, 2944
	mov ecx, 1864
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 144
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -504
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1360
	mov edx, 2944
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, -72
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 432
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -432
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 72
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1720
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1720
	mov r12, rsi
	mov esi, 1792
	mov edx, 2008
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1720
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1360
	mov edx, 1288
	mov ecx, 1432
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1432
	mov edx, 2008
	mov ecx, 1432
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1936
	mov ecx, 1720
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+1504], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+1512], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+1520], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+1528], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+1536], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+1544], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+1552], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+1560], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+1568], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+1600], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+1608], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+1616], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+1624], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+1632], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+1640], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+1648], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+1656], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+1664], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+1672], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+1680], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+1688], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+1696], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+1704], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+1712], rax
	cmp rbx, 6
	je 25f
	cmp rbx, 5
	je 27f
	cmp rbx, 4
	je 29f
	cmp rbx, 3
	je 211f
	cmp rbx, 2
	je 213f
	cmp rbx, 1
	je 215f
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+7624], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+7632], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+7640], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+7648], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+7656], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+7664], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+7672], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+7680], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+7688], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7696], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7704], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7712], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7720], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7728], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7736], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7744], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7752], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7760], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+7768], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+7776], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+7784], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+7792], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+7800], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+7808], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+7816], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+7824], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+7832], rax
	jmp 216f
215:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+7408], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+7416], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+7424], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+7432], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+7440], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+7448], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+7456], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+7464], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+7472], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7480], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7488], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7496], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7504], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7512], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7520], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7528], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7536], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7544], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+7552], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+7560], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+7568], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+7576], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+7584], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+7592], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+7600], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+7608], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+7616], rax
216:
	jmp 214f
213:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+7192], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+7200], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+7208], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+7216], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+7224], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+7232], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+7240], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+7248], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+7256], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7264], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7272], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7280], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7288], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7296], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7304], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7312], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7320], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7328], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+7336], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+7344], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+7352], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+7360], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+7368], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+7376], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+7384], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+7392], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+7400], rax
214:
	jmp 212f
211:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+6976], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+6984], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+6992], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+7000], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+7008], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+7016], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+7024], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+7032], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+7040], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7048], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7056], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7064], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7072], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7080], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7088], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7096], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7104], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7112], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+7120], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+7128], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+7136], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+7144], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+7152], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+7160], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+7168], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+7176], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+7184], rax
212:
	jmp 210f
29:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+6760], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+6768], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+6776], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+6784], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+6792], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+6800], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+6808], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+6816], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+6824], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6832], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6840], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6848], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6856], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6864], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6872], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6880], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6888], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6896], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+6904], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+6912], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+6920], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+6928], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+6936], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+6944], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+6952], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+6960], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+6968], rax
210:
	jmp 28f
27:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+6544], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+6552], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+6560], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+6568], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+6576], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+6584], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+6592], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+6600], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+6608], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6616], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6624], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6632], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6640], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6648], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6656], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6664], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6672], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6680], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+6688], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+6696], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+6704], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+6712], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+6720], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+6728], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+6736], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+6744], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+6752], rax
28:
	jmp 26f
25:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+6328], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+6336], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+6344], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+6352], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+6360], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+6368], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+6376], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+6384], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+6392], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6400], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6408], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6416], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6424], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6432], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6440], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6448], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6456], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6464], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+6472], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+6480], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+6488], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+6496], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+6504], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+6512], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+6520], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+6528], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+6536], rax
26:
	test rbx, rbx
	jne 24b
	mov rax, QWORD PTR [rdi+6256]
	mov QWORD PTR [rdi+1432], rax
	mov rax, QWORD PTR [rdi+6264]
	mov QWORD PTR [rdi+1440], rax
	mov rax, QWORD PTR [rdi+6272]
	mov QWORD PTR [rdi+1448], rax
	mov rax, QWORD PTR [rdi+6280]
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+6288]
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+6296]
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+6304]
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+6312]
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+6320]
	mov QWORD PTR [rdi+1496], rax
	mov rax, QWORD PTR [rdi+6472]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6480]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6488]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6496]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6504]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6512]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6520]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6528]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6536]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1720
	mov edx, 1432
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6688]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6696]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6704]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6712]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6720]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6728]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6736]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6744]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6752]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1792
	mov edx, 1720
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6904]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6912]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6920]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6928]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6936]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6944]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6952]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6960]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6968]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1864
	mov edx, 1792
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7120]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7128]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7136]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7144]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7152]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7160]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7168]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7176]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7184]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1936
	mov edx, 1864
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7336]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7344]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7352]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7360]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7368]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7376]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7384]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7392]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7400]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 2008
	mov edx, 1936
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7552]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7560]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7568]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7576]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7584]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7592]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7600]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7608]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7616]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 2080
	mov edx, 2008
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7768]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7776]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7784]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7792]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7800]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7808]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7816]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7824]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7832]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1216
	mov edx, 2080
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+5320]
	mov QWORD PTR [rdi+4472], rax
	mov rax, QWORD PTR [rdi+5328]
	mov QWORD PTR [rdi+4480], rax
	mov rax, QWORD PTR [rdi+5336]
	mov QWORD PTR [rdi+4488], rax
	mov rax, QWORD PTR [rdi+5344]
	mov QWORD PTR [rdi+4496], rax
	mov rax, QWORD PTR [rdi+5352]
	mov QWORD PTR [rdi+4504], rax
	mov rax, QWORD PTR [rdi+5360]
	mov QWORD PTR [rdi+4512], rax
	mov rax, QWORD PTR [rdi+5368]
	mov QWORD PTR [rdi+4520], rax
	mov rax, QWORD PTR [rdi+5376]
	mov QWORD PTR [rdi+4528], rax
	mov rax, QWORD PTR [rdi+5384]
	mov QWORD PTR [rdi+4536], rax
	mov rax, QWORD PTR [rdi+5392]
	mov QWORD PTR [rdi+4544], rax
	mov rax, QWORD PTR [rdi+5400]
	mov QWORD PTR [rdi+4552], rax
	mov rax, QWORD PTR [rdi+5408]
	mov QWORD PTR [rdi+4560], rax
	mov rax, QWORD PTR [rdi+5416]
	mov QWORD PTR [rdi+4568], rax
	mov rax, QWORD PTR [rdi+5424]
	mov QWORD PTR [rdi+4576], rax
	mov rax, QWORD PTR [rdi+5432]
	mov QWORD PTR [rdi+4584], rax
	mov rax, QWORD PTR [rdi+5440]
	mov QWORD PTR [rdi+4592], rax
	mov rax, QWORD PTR [rdi+5448]
	mov QWORD PTR [rdi+4600], rax
	mov rax, QWORD PTR [rdi+5456]
	mov QWORD PTR [rdi+4608], rax
	mov rax, QWORD PTR [rdi+5464]
	mov QWORD PTR [rdi+4616], rax
	mov rax, QWORD PTR [rdi+5472]
	mov QWORD PTR [rdi+4624], rax
	mov rax, QWORD PTR [rdi+5480]
	mov QWORD PTR [rdi+4632], rax
	mov rax, QWORD PTR [rdi+5488]
	mov QWORD PTR [rdi+4640], rax
	mov rax, QWORD PTR [rdi+5496]
	mov QWORD PTR [rdi+4648], rax
	mov rax, QWORD PTR [rdi+5504]
	mov QWORD PTR [rdi+4656], rax
	mov rax, QWORD PTR [rdi+5512]
	mov QWORD PTR [rdi+4664], rax
	mov rax, QWORD PTR [rdi+5520]
	mov QWORD PTR [rdi+4672], rax
	mov rax, QWORD PTR [rdi+5528]
	mov QWORD PTR [rdi+4680], rax
	mov rax, QWORD PTR [rdi+5536]
	mov QWORD PTR [rdi+4688], rax
	mov rax, QWORD PTR [rdi+5544]
	mov QWORD PTR [rdi+4696], rax
	mov rax, QWORD PTR [rdi+5552]
	mov QWORD PTR [rdi+4704], rax
	mov rax, QWORD PTR [rdi+5560]
	mov QWORD PTR [rdi+4712], rax
	mov rax, QWORD PTR [rdi+5568]
	mov QWORD PTR [rdi+4720], rax
	mov rax, QWORD PTR [rdi+5576]
	mov QWORD PTR [rdi+4728], rax
	mov rax, QWORD PTR [rdi+5584]
	mov QWORD PTR [rdi+4736], rax
	mov rax, QWORD PTR [rdi+5592]
	mov QWORD PTR [rdi+4744], rax
	mov rax, QWORD PTR [rdi+5600]
	mov QWORD PTR [rdi+4752], rax
	mov rax, QWORD PTR [rdi+5608]
	mov QWORD PTR [rdi+4760], rax
	mov rax, QWORD PTR [rdi+5616]
	mov QWORD PTR [rdi+4768], rax
	mov rax, QWORD PTR [rdi+5624]
	mov QWORD PTR [rdi+4776], rax
	mov rax, QWORD PTR [rdi+5632]
	mov QWORD PTR [rdi+4784], rax
	mov rax, QWORD PTR [rdi+5640]
	mov QWORD PTR [rdi+4792], rax
	mov rax, QWORD PTR [rdi+5648]
	mov QWORD PTR [rdi+4800], rax
	mov rax, QWORD PTR [rdi+5656]
	mov QWORD PTR [rdi+4808], rax
	mov rax, QWORD PTR [rdi+5664]
	mov QWORD PTR [rdi+4816], rax
	mov rax, QWORD PTR [rdi+5672]
	mov QWORD PTR [rdi+4824], rax
	mov rax, QWORD PTR [rdi+5680]
	mov QWORD PTR [rdi+4832], rax
	mov rax, QWORD PTR [rdi+5688]
	mov QWORD PTR [rdi+4840], rax
	mov rax, QWORD PTR [rdi+2224]
	mov QWORD PTR [rdi+4848], rax
	mov rax, QWORD PTR [rdi+2232]
	mov QWORD PTR [rdi+4856], rax
	mov rax, QWORD PTR [rdi+2240]
	mov QWORD PTR [rdi+4864], rax
	mov rax, QWORD PTR [rdi+2248]
	mov QWORD PTR [rdi+4872], rax
	mov rax, QWORD PTR [rdi+2256]
	mov QWORD PTR [rdi+4880], rax
	mov rax, QWORD PTR [rdi+2264]
	mov QWORD PTR [rdi+4888], rax
	mov rax, QWORD PTR [rdi+2272]
	mov QWORD PTR [rdi+4896], rax
	mov rax, QWORD PTR [rdi+2280]
	mov QWORD PTR [rdi+4904], rax
	mov rax, QWORD PTR [rdi+2288]
	mov QWORD PTR [rdi+4912], rax
	call {vg_p521_inv_mod_p}
	mov rax, QWORD PTR [rdi+2152]
	mov QWORD PTR [rdi+1504], rax
	mov rax, QWORD PTR [rdi+2160]
	mov QWORD PTR [rdi+1512], rax
	mov rax, QWORD PTR [rdi+2168]
	mov QWORD PTR [rdi+1520], rax
	mov rax, QWORD PTR [rdi+2176]
	mov QWORD PTR [rdi+1528], rax
	mov rax, QWORD PTR [rdi+2184]
	mov QWORD PTR [rdi+1536], rax
	mov rax, QWORD PTR [rdi+2192]
	mov QWORD PTR [rdi+1544], rax
	mov rax, QWORD PTR [rdi+2200]
	mov QWORD PTR [rdi+1552], rax
	mov rax, QWORD PTR [rdi+2208]
	mov QWORD PTR [rdi+1560], rax
	mov rax, QWORD PTR [rdi+2216]
	mov QWORD PTR [rdi+1568], rax
	mov rax, QWORD PTR [rdi+4848]
	mov QWORD PTR [rdi+2224], rax
	mov rax, QWORD PTR [rdi+4856]
	mov QWORD PTR [rdi+2232], rax
	mov rax, QWORD PTR [rdi+4864]
	mov QWORD PTR [rdi+2240], rax
	mov rax, QWORD PTR [rdi+4872]
	mov QWORD PTR [rdi+2248], rax
	mov rax, QWORD PTR [rdi+4880]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rdi+4888]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rdi+4896]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rdi+4904]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rdi+4912]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rdi+4472]
	mov QWORD PTR [rdi+5320], rax
	mov rax, QWORD PTR [rdi+4480]
	mov QWORD PTR [rdi+5328], rax
	mov rax, QWORD PTR [rdi+4488]
	mov QWORD PTR [rdi+5336], rax
	mov rax, QWORD PTR [rdi+4496]
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+4504]
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+4512]
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+4520]
	mov QWORD PTR [rdi+5368], rax
	mov rax, QWORD PTR [rdi+4528]
	mov QWORD PTR [rdi+5376], rax
	mov rax, QWORD PTR [rdi+4536]
	mov QWORD PTR [rdi+5384], rax
	mov rax, QWORD PTR [rdi+4544]
	mov QWORD PTR [rdi+5392], rax
	mov rax, QWORD PTR [rdi+4552]
	mov QWORD PTR [rdi+5400], rax
	mov rax, QWORD PTR [rdi+4560]
	mov QWORD PTR [rdi+5408], rax
	mov rax, QWORD PTR [rdi+4568]
	mov QWORD PTR [rdi+5416], rax
	mov rax, QWORD PTR [rdi+4576]
	mov QWORD PTR [rdi+5424], rax
	mov rax, QWORD PTR [rdi+4584]
	mov QWORD PTR [rdi+5432], rax
	mov rax, QWORD PTR [rdi+4592]
	mov QWORD PTR [rdi+5440], rax
	mov rax, QWORD PTR [rdi+4600]
	mov QWORD PTR [rdi+5448], rax
	mov rax, QWORD PTR [rdi+4608]
	mov QWORD PTR [rdi+5456], rax
	mov rax, QWORD PTR [rdi+4616]
	mov QWORD PTR [rdi+5464], rax
	mov rax, QWORD PTR [rdi+4624]
	mov QWORD PTR [rdi+5472], rax
	mov rax, QWORD PTR [rdi+4632]
	mov QWORD PTR [rdi+5480], rax
	mov rax, QWORD PTR [rdi+4640]
	mov QWORD PTR [rdi+5488], rax
	mov rax, QWORD PTR [rdi+4648]
	mov QWORD PTR [rdi+5496], rax
	mov rax, QWORD PTR [rdi+4656]
	mov QWORD PTR [rdi+5504], rax
	mov rax, QWORD PTR [rdi+4664]
	mov QWORD PTR [rdi+5512], rax
	mov rax, QWORD PTR [rdi+4672]
	mov QWORD PTR [rdi+5520], rax
	mov rax, QWORD PTR [rdi+4680]
	mov QWORD PTR [rdi+5528], rax
	mov rax, QWORD PTR [rdi+4688]
	mov QWORD PTR [rdi+5536], rax
	mov rax, QWORD PTR [rdi+4696]
	mov QWORD PTR [rdi+5544], rax
	mov rax, QWORD PTR [rdi+4704]
	mov QWORD PTR [rdi+5552], rax
	mov rax, QWORD PTR [rdi+4712]
	mov QWORD PTR [rdi+5560], rax
	mov rax, QWORD PTR [rdi+4720]
	mov QWORD PTR [rdi+5568], rax
	mov rax, QWORD PTR [rdi+4728]
	mov QWORD PTR [rdi+5576], rax
	mov rax, QWORD PTR [rdi+4736]
	mov QWORD PTR [rdi+5584], rax
	mov rax, QWORD PTR [rdi+4744]
	mov QWORD PTR [rdi+5592], rax
	mov rax, QWORD PTR [rdi+4752]
	mov QWORD PTR [rdi+5600], rax
	mov rax, QWORD PTR [rdi+4760]
	mov QWORD PTR [rdi+5608], rax
	mov rax, QWORD PTR [rdi+4768]
	mov QWORD PTR [rdi+5616], rax
	mov rax, QWORD PTR [rdi+4776]
	mov QWORD PTR [rdi+5624], rax
	mov rax, QWORD PTR [rdi+4784]
	mov QWORD PTR [rdi+5632], rax
	mov rax, QWORD PTR [rdi+4792]
	mov QWORD PTR [rdi+5640], rax
	mov rax, QWORD PTR [rdi+4800]
	mov QWORD PTR [rdi+5648], rax
	mov rax, QWORD PTR [rdi+4808]
	mov QWORD PTR [rdi+5656], rax
	mov rax, QWORD PTR [rdi+4816]
	mov QWORD PTR [rdi+5664], rax
	mov rax, QWORD PTR [rdi+4824]
	mov QWORD PTR [rdi+5672], rax
	mov rax, QWORD PTR [rdi+4832]
	mov QWORD PTR [rdi+5680], rax
	mov rax, QWORD PTR [rdi+4840]
	mov QWORD PTR [rdi+5688], rax
	mov r12, rsi
	mov esi, 1288
	mov edx, 1504
	mov ecx, 2080
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7768]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7776]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7784]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7792]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7800]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7808]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7816]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7824]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7832]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1504
	mov edx, 1504
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7624]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7632]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7640]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7648]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7656]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7664]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7672]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7680]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7688]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7624], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7632], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7640], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7648], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7656], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7664], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7672], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7680], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7688], rax
	mov rax, QWORD PTR [rdi+7696]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7704]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7712]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7720]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7728]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7736]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7744]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7752]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7760]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7696], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7704], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7712], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7720], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7728], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7736], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7744], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7752], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7760], rax
	mov r12, rsi
	mov esi, 1288
	mov edx, 1504
	mov ecx, 2008
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7552]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7560]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7568]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7576]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7584]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7592]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7600]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7608]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7616]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1504
	mov edx, 1504
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7408]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7416]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7424]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7432]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7440]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7448]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7456]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7464]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7472]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7408], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7416], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7424], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7432], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7440], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7448], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7456], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7464], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7472], rax
	mov rax, QWORD PTR [rdi+7480]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7488]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7496]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7504]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7512]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7520]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7528]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7536]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7544]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7480], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7488], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7496], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7504], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7512], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7520], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7528], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7536], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7544], rax
	mov r12, rsi
	mov esi, 1288
	mov edx, 1504
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7336]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7344]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7352]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7360]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7368]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7376]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7384]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7392]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7400]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1504
	mov edx, 1504
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7192]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7200]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7208]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7216]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7224]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7232]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7240]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7248]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7256]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7192], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7200], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7208], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7216], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7224], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7232], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7240], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7248], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7256], rax
	mov rax, QWORD PTR [rdi+7264]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7272]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7280]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7288]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7296]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7304]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7312]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7320]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7328]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7264], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7272], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7280], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7288], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7296], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7304], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7312], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7320], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7328], rax
	mov r12, rsi
	mov esi, 1288
	mov edx, 1504
	mov ecx, 1864
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7120]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7128]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7136]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7144]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7152]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7160]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7168]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7176]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7184]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1504
	mov edx, 1504
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6976]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6984]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6992]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7000]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7008]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7016]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7024]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7032]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7040]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6976], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6984], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6992], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7000], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7008], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7016], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7024], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7032], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7040], rax
	mov rax, QWORD PTR [rdi+7048]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7056]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7064]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7072]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7080]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7088]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7096]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7104]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7112]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7048], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7056], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7064], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7072], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7080], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7088], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7096], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7104], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7112], rax
	mov r12, rsi
	mov esi, 1288
	mov edx, 1504
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6904]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6912]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6920]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6928]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6936]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6944]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6952]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6960]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6968]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1504
	mov edx, 1504
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6760]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6768]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6776]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6784]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6792]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6800]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6808]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6816]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6824]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6760], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6768], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6776], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6784], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6792], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6800], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6808], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6816], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6824], rax
	mov rax, QWORD PTR [rdi+6832]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6840]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6848]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6856]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6864]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6872]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6880]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6888]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6896]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6832], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6840], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6848], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6856], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6864], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6872], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6880], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6888], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6896], rax
	mov r12, rsi
	mov esi, 1288
	mov edx, 1504
	mov ecx, 1720
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6688]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6696]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6704]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6712]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6720]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6728]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6736]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6744]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6752]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1504
	mov edx, 1504
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6544]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6552]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6560]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6568]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6576]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6584]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6592]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6600]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6608]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6544], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6552], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6560], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6568], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6576], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6584], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6592], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6600], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6608], rax
	mov rax, QWORD PTR [rdi+6616]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6624]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6632]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6640]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6648]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6656]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6664]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6672]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6680]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6616], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6624], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6632], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6640], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6648], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6656], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6664], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6672], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6680], rax
	mov r12, rsi
	mov esi, 1288
	mov edx, 1504
	mov ecx, 1432
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6472]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6480]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6488]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6496]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6504]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6512]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6520]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6528]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6536]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1504
	mov edx, 1504
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6328]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6336]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6344]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6352]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6360]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6368]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6376]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6384]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6392]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6328], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6336], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6344], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6352], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6360], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6368], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6376], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6384], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6392], rax
	mov rax, QWORD PTR [rdi+6400]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6408]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6416]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6424]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6432]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6440]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6448]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6456]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6464]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6400], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6408], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6416], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6424], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6432], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6440], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6448], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6456], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6464], rax
	mov rax, QWORD PTR [rdi+6112]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6120]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6128]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6136]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6144]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6152]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6160]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6168]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6176]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1504
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6112], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6120], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6128], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6136], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6144], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6152], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6160], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6168], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6176], rax
	mov rax, QWORD PTR [rdi+6184]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6192]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6200]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6208]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6216]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6224]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6232]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6240]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6248]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1504
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6184], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6192], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6200], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6208], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6216], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6224], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6232], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6240], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6248], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+6256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6280], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6296], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6320], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+6472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6488], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6496], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6504], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6512], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6536], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+6688], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6696], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6704], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6712], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6720], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6728], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6736], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6752], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+6904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6920], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6928], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6936], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6944], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6952], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6960], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6968], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+7120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7128], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7136], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7184], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+7336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7344], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7352], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7400], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+7552], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7560], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7576], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7584], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7592], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7600], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7608], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7616], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+7768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7776], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7784], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7792], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7800], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7808], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7816], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1080], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1088], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1104], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1112], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1184], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1248], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1280], rax
	mov ebx, 131
217:
	sub rbx, 1
	add rbx, 8192
218:
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1144
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov r12, rsi
	mov esi, 1792
	mov edx, 1144
	mov ecx, 1144
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1072
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, -648
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	mov r12, rsi
	mov esi, 1432
	mov edx, 1432
	mov ecx, 1432
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1792
	mov edx, 1792
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 288
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -288
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	mov r12, rsi
	mov esi, 1360
	mov edx, 1936
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 432
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1720
	mov edx, 1432
	mov ecx, 1432
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 432
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 432
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1072
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1216
	mov r12, rsi
	mov esi, 1792
	mov edx, 1360
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 1072
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1288
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, -864
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1072
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 864
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	mov r12, rsi
	mov esi, 1216
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	mov r12, rsi
	mov esi, 1072
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	add rdi, 1216
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1216
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 792
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -792
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1072
	mov r12, rsi
	mov esi, 1792
	mov edx, 1792
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 792
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -792
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1072
	add rdi, 1216
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1216
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -792
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1144
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	mov r12, rsi
	mov esi, 1144
	mov edx, 1936
	mov ecx, 1144
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1144
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1144
	sub rbx, 4096
	cmp rbx, 4096
	jae 218b
	mov rax, rbx
	mov ecx, 4
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+5323]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+5322]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+5321]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+5320]
	add rax, rdx
	sub rax, 8
	mov rdx, rax
	shr rdx, 63
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	mov r8, rax
	mov rdx, rdi
	add rdx, 6112
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	mov ecx, 1
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+16]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+32]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+48]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+64]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+80]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+96]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+112]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+128]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+144]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+160]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+176]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+192]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+200]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 2
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+216]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+232]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+248]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+264]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+280]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+296]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+312]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+328]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+344]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+360]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+376]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+392]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+408]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+416]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 3
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+432]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+448]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+464]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+480]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+496]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+512]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+528]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+544]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+560]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+576]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+592]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+608]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+624]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+632]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 4
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+648]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+664]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+680]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+696]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+712]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+728]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+744]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+760]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+776]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+792]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+808]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+824]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+840]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+848]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 5
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+864]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+880]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+896]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+912]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+928]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+944]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+960]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+976]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+992]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1008]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1024]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1040]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1056]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1064]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 6
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1080]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1096]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1112]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1128]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1144]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1160]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1176]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1192]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1208]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1224]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1240]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1256]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1272]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1280]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 7
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1296]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1312]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1328]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1344]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1360]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1376]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1392]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1408]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1424]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1440]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1456]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1472]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1488]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1496]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 8
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1512]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1528]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1544]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1560]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1576]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1592]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1608]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1624]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1640]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1656]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1672]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1688]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1704]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1712]
	pand xmm14, xmm15
	por xmm13, xmm14
	movdqu XMMWORD PTR [rdi+1504], xmm0
	movdqu XMMWORD PTR [rdi+1520], xmm1
	movdqu XMMWORD PTR [rdi+1536], xmm2
	movdqu XMMWORD PTR [rdi+1552], xmm3
	movdqu XMMWORD PTR [rdi+1568], xmm4
	movdqu XMMWORD PTR [rdi+1584], xmm5
	movdqu XMMWORD PTR [rdi+1600], xmm6
	movdqu XMMWORD PTR [rdi+1616], xmm7
	movdqu XMMWORD PTR [rdi+1632], xmm8
	movdqu XMMWORD PTR [rdi+1648], xmm9
	movdqu XMMWORD PTR [rdi+1664], xmm10
	movdqu XMMWORD PTR [rdi+1680], xmm11
	movdqu XMMWORD PTR [rdi+1696], xmm12
	movdqu XMMWORD PTR [rdi+1704], xmm13
	mov rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movabs rax, 36028797018963968
	and rax, rcx
	or rax, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+1576], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+1584], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+1592], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+1600], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+1608], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+1616], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1624]
	mov QWORD PTR [rdi+1624], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1632]
	mov QWORD PTR [rdi+1632], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1640]
	mov QWORD PTR [rdi+1640], rax
	add rdi, 280
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 1296
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2224
	mov rax, rbx
	mov ecx, 4
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+5323]
	sub rax, 1
	mov rcx, rax
	mov rax, QWORD PTR [rdi+1576]
	mov rdx, QWORD PTR [rdi+2224]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rdi+1584]
	mov rdx, QWORD PTR [rdi+2232]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rdi+1592]
	mov rdx, QWORD PTR [rdi+2240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rdi+1600]
	mov rdx, QWORD PTR [rdi+2248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1600], rax
	mov rax, QWORD PTR [rdi+1608]
	mov rdx, QWORD PTR [rdi+2256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1608], rax
	mov rax, QWORD PTR [rdi+1616]
	mov rdx, QWORD PTR [rdi+2264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1616], rax
	mov rax, QWORD PTR [rdi+1624]
	mov rdx, QWORD PTR [rdi+2272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1624], rax
	mov rax, QWORD PTR [rdi+1632]
	mov rdx, QWORD PTR [rdi+2280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1632], rax
	mov rax, QWORD PTR [rdi+1640]
	mov rdx, QWORD PTR [rdi+2288]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1640], rax
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1504
	mov ecx, 1720
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1216
	mov ecx, 1720
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1576
	mov ecx, 1864
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -720
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 720
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -720
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 720
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	mov r12, rsi
	mov esi, 1936
	mov edx, 1792
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2008
	mov edx, 1792
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1936
	mov edx, 1072
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1288
	mov edx, 1864
	mov ecx, 1864
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 720
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -720
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 144
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2080
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 792
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -792
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	mov r12, rsi
	mov esi, 1936
	mov edx, 1864
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2008
	mov edx, 1144
	mov ecx, 2008
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1432
	mov edx, 1216
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rdx, QWORD PTR [rdi+1648]
	or rdx, QWORD PTR [rdi+1656]
	or rdx, QWORD PTR [rdi+1664]
	or rdx, QWORD PTR [rdi+1672]
	or rdx, QWORD PTR [rdi+1680]
	or rdx, QWORD PTR [rdi+1688]
	or rdx, QWORD PTR [rdi+1696]
	or rdx, QWORD PTR [rdi+1704]
	or rdx, QWORD PTR [rdi+1712]
	cmp rdx, 1
	sbb rdx, rdx
	mov rcx, rdx
	mov rax, QWORD PTR [rdi+1288]
	mov rdx, QWORD PTR [rdi+1072]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1288], rax
	mov rax, QWORD PTR [rdi+1296]
	mov rdx, QWORD PTR [rdi+1080]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1296], rax
	mov rax, QWORD PTR [rdi+1304]
	mov rdx, QWORD PTR [rdi+1088]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1304], rax
	mov rax, QWORD PTR [rdi+1312]
	mov rdx, QWORD PTR [rdi+1096]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1312], rax
	mov rax, QWORD PTR [rdi+1320]
	mov rdx, QWORD PTR [rdi+1104]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1320], rax
	mov rax, QWORD PTR [rdi+1328]
	mov rdx, QWORD PTR [rdi+1112]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1328], rax
	mov rax, QWORD PTR [rdi+1336]
	mov rdx, QWORD PTR [rdi+1120]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1336], rax
	mov rax, QWORD PTR [rdi+1344]
	mov rdx, QWORD PTR [rdi+1128]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1344], rax
	mov rax, QWORD PTR [rdi+1352]
	mov rdx, QWORD PTR [rdi+1136]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1352], rax
	mov rax, QWORD PTR [rdi+1360]
	mov rdx, QWORD PTR [rdi+1144]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+1368]
	mov rdx, QWORD PTR [rdi+1152]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+1376]
	mov rdx, QWORD PTR [rdi+1160]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+1384]
	mov rdx, QWORD PTR [rdi+1168]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+1392]
	mov rdx, QWORD PTR [rdi+1176]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+1400]
	mov rdx, QWORD PTR [rdi+1184]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+1408]
	mov rdx, QWORD PTR [rdi+1192]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+1416]
	mov rdx, QWORD PTR [rdi+1200]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+1424]
	mov rdx, QWORD PTR [rdi+1208]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1424], rax
	mov rax, QWORD PTR [rdi+1432]
	mov rdx, QWORD PTR [rdi+1216]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1432], rax
	mov rax, QWORD PTR [rdi+1440]
	mov rdx, QWORD PTR [rdi+1224]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1440], rax
	mov rax, QWORD PTR [rdi+1448]
	mov rdx, QWORD PTR [rdi+1232]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1448], rax
	mov rax, QWORD PTR [rdi+1456]
	mov rdx, QWORD PTR [rdi+1240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+1464]
	mov rdx, QWORD PTR [rdi+1248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+1472]
	mov rdx, QWORD PTR [rdi+1256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+1480]
	mov rdx, QWORD PTR [rdi+1264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+1488]
	mov rdx, QWORD PTR [rdi+1272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+1496]
	mov rdx, QWORD PTR [rdi+1280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1496], rax
	mov rdx, QWORD PTR [rdi+1216]
	or rdx, QWORD PTR [rdi+1224]
	or rdx, QWORD PTR [rdi+1232]
	or rdx, QWORD PTR [rdi+1240]
	or rdx, QWORD PTR [rdi+1248]
	or rdx, QWORD PTR [rdi+1256]
	or rdx, QWORD PTR [rdi+1264]
	or rdx, QWORD PTR [rdi+1272]
	or rdx, QWORD PTR [rdi+1280]
	cmp rdx, 1
	sbb rdx, rdx
	mov rcx, rdx
	mov rax, QWORD PTR [rdi+1288]
	mov rdx, QWORD PTR [rdi+1504]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov rdx, QWORD PTR [rdi+1512]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov rdx, QWORD PTR [rdi+1520]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov rdx, QWORD PTR [rdi+1528]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov rdx, QWORD PTR [rdi+1536]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov rdx, QWORD PTR [rdi+1544]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov rdx, QWORD PTR [rdi+1552]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov rdx, QWORD PTR [rdi+1560]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov rdx, QWORD PTR [rdi+1568]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov rdx, QWORD PTR [rdi+1576]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov rdx, QWORD PTR [rdi+1584]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov rdx, QWORD PTR [rdi+1592]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov rdx, QWORD PTR [rdi+1600]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov rdx, QWORD PTR [rdi+1608]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov rdx, QWORD PTR [rdi+1616]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov rdx, QWORD PTR [rdi+1624]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov rdx, QWORD PTR [rdi+1632]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov rdx, QWORD PTR [rdi+1640]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov rdx, QWORD PTR [rdi+1648]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov rdx, QWORD PTR [rdi+1656]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov rdx, QWORD PTR [rdi+1664]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov rdx, QWORD PTR [rdi+1672]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov rdx, QWORD PTR [rdi+1680]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov rdx, QWORD PTR [rdi+1688]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov rdx, QWORD PTR [rdi+1696]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov rdx, QWORD PTR [rdi+1704]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov rdx, QWORD PTR [rdi+1712]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1280], rax
	cmp rbx, 1
	jne 217b
	sub rbx, 1
	add rbx, 8192
219:
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1144
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov r12, rsi
	mov esi, 1792
	mov edx, 1144
	mov ecx, 1144
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1072
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, -648
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	mov r12, rsi
	mov esi, 1432
	mov edx, 1432
	mov ecx, 1432
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1792
	mov edx, 1792
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 288
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -288
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	mov r12, rsi
	mov esi, 1360
	mov edx, 1936
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 432
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1720
	mov edx, 1432
	mov ecx, 1432
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 432
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 432
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1072
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1216
	mov r12, rsi
	mov esi, 1792
	mov edx, 1360
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 1072
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1288
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, -864
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1072
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 864
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	mov r12, rsi
	mov esi, 1216
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	mov r12, rsi
	mov esi, 1072
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	add rdi, 1216
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1216
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 792
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -792
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1072
	mov r12, rsi
	mov esi, 1792
	mov edx, 1792
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 792
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -792
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1072
	add rdi, 1216
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1216
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -792
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1144
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	mov r12, rsi
	mov esi, 1144
	mov edx, 1936
	mov ecx, 1144
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1144
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1144
	sub rbx, 4096
	cmp rbx, 4096
	jae 219b
	mov r12, rsi
	mov esi, 1288
	mov edx, 1072
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1432
	mov edx, 1720
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1144
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -864
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 1080
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+1280], rax
	mov rdx, QWORD PTR [rdi+1216]
	or rdx, QWORD PTR [rdi+1224]
	or rdx, QWORD PTR [rdi+1232]
	or rdx, QWORD PTR [rdi+1240]
	or rdx, QWORD PTR [rdi+1248]
	or rdx, QWORD PTR [rdi+1256]
	or rdx, QWORD PTR [rdi+1264]
	or rdx, QWORD PTR [rdi+1272]
	or rdx, QWORD PTR [rdi+1280]
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1144]
	movabs r8, 36028797018963968
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1152]
	movabs r8, 0
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1160]
	movabs r8, 0
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1168]
	movabs r8, 0
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1176]
	movabs r8, 0
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1184]
	movabs r8, 0
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1192]
	movabs r8, 0
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1200]
	movabs r8, 0
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1208]
	movabs r8, 0
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1208], rax
	mov rax, rbx
	mov ecx, 4
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+5323]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+5322]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+5321]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+5320]
	add rax, rdx
	sub rax, 8
	mov rdx, rax
	shr rdx, 63
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	mov r8, rax
	mov rdx, rdi
	add rdx, 6112
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	mov ecx, 1
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+16]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+32]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+48]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+64]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+80]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+96]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+112]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+128]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+144]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+160]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+176]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+192]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+200]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 2
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+216]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+232]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+248]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+264]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+280]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+296]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+312]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+328]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+344]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+360]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+376]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+392]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+408]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+416]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 3
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+432]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+448]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+464]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+480]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+496]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+512]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+528]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+544]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+560]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+576]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+592]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+608]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+624]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+632]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 4
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+648]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+664]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+680]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+696]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+712]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+728]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+744]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+760]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+776]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+792]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+808]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+824]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+840]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+848]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 5
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+864]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+880]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+896]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+912]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+928]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+944]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+960]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+976]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+992]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1008]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1024]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1040]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1056]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1064]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 6
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1080]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1096]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1112]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1128]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1144]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1160]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1176]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1192]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1208]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1224]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1240]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1256]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1272]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1280]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 7
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1296]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1312]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1328]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1344]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1360]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1376]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1392]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1408]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1424]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1440]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1456]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1472]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1488]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1496]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 8
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1512]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1528]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1544]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1560]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1576]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1592]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1608]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1624]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1640]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1656]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1672]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1688]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1704]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1712]
	pand xmm14, xmm15
	por xmm13, xmm14
	movdqu XMMWORD PTR [rdi+1504], xmm0
	movdqu XMMWORD PTR [rdi+1520], xmm1
	movdqu XMMWORD PTR [rdi+1536], xmm2
	movdqu XMMWORD PTR [rdi+1552], xmm3
	movdqu XMMWORD PTR [rdi+1568], xmm4
	movdqu XMMWORD PTR [rdi+1584], xmm5
	movdqu XMMWORD PTR [rdi+1600], xmm6
	movdqu XMMWORD PTR [rdi+1616], xmm7
	movdqu XMMWORD PTR [rdi+1632], xmm8
	movdqu XMMWORD PTR [rdi+1648], xmm9
	movdqu XMMWORD PTR [rdi+1664], xmm10
	movdqu XMMWORD PTR [rdi+1680], xmm11
	movdqu XMMWORD PTR [rdi+1696], xmm12
	movdqu XMMWORD PTR [rdi+1704], xmm13
	mov rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movabs rax, 36028797018963968
	and rax, rcx
	or rax, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+1576], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+1584], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+1592], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+1600], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+1608], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+1616], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1624]
	mov QWORD PTR [rdi+1624], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1632]
	mov QWORD PTR [rdi+1632], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1640]
	mov QWORD PTR [rdi+1640], rax
	add rdi, 280
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 1296
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2224
	mov rax, rbx
	mov ecx, 4
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+5323]
	sub rax, 1
	mov rcx, rax
	mov rax, QWORD PTR [rdi+1576]
	mov rdx, QWORD PTR [rdi+2224]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rdi+1584]
	mov rdx, QWORD PTR [rdi+2232]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rdi+1592]
	mov rdx, QWORD PTR [rdi+2240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rdi+1600]
	mov rdx, QWORD PTR [rdi+2248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1600], rax
	mov rax, QWORD PTR [rdi+1608]
	mov rdx, QWORD PTR [rdi+2256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1608], rax
	mov rax, QWORD PTR [rdi+1616]
	mov rdx, QWORD PTR [rdi+2264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1616], rax
	mov rax, QWORD PTR [rdi+1624]
	mov rdx, QWORD PTR [rdi+2272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1624], rax
	mov rax, QWORD PTR [rdi+1632]
	mov rdx, QWORD PTR [rdi+2280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1632], rax
	mov rax, QWORD PTR [rdi+1640]
	mov rdx, QWORD PTR [rdi+2288]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1640], rax
	mov r12, rsi
	mov esi, 1720
	mov edx, 1072
	mov ecx, 1504
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1144
	mov ecx, 1576
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1216
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 792
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1504
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 2008
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1144
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 792
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	add rdi, 1576
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 2008
	mov edx, 2008
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 2008
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -720
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 720
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1504
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -288
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1288
	mov edx, 1288
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1432
	mov edx, 2944
	mov ecx, 1864
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 144
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -504
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1360
	mov edx, 2944
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, -72
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 432
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -432
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 72
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1720
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1720
	mov r12, rsi
	mov esi, 1792
	mov edx, 2008
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1720
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1360
	mov edx, 1288
	mov ecx, 1432
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1432
	mov edx, 2008
	mov ecx, 1432
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1936
	mov ecx, 1720
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+1280], rax
	call {vg_p521_inv_mod_p}
	mov r12, rsi
	mov esi, 2512
	mov edx, 1072
	mov ecx, 2152
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2584
	mov edx, 2512
	mov ecx, 352
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rdx, QWORD PTR [rdi+2368]
	sub rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2376]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2384]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2392]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2400]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2408]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2416]
	sbb rdx, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+2424]
	sbb rdx, QWORD PTR [rdi+192]
	mov rdx, QWORD PTR [rdi+2432]
	sbb rdx, QWORD PTR [rdi+200]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+2368]
	or rdx, QWORD PTR [rdi+2376]
	or rdx, QWORD PTR [rdi+2384]
	or rdx, QWORD PTR [rdi+2392]
	or rdx, QWORD PTR [rdi+2400]
	or rdx, QWORD PTR [rdi+2408]
	or rdx, QWORD PTR [rdi+2416]
	or rdx, QWORD PTR [rdi+2424]
	or rdx, QWORD PTR [rdi+2432]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+1216]
	or rdx, QWORD PTR [rdi+1224]
	or rdx, QWORD PTR [rdi+1232]
	or rdx, QWORD PTR [rdi+1240]
	or rdx, QWORD PTR [rdi+1248]
	or rdx, QWORD PTR [rdi+1256]
	or rdx, QWORD PTR [rdi+1264]
	or rdx, QWORD PTR [rdi+1272]
	or rdx, QWORD PTR [rdi+1280]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rcx, QWORD PTR [rdi+3232]
	mov rax, QWORD PTR [rdi+2584]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+58], rax
	mov rax, QWORD PTR [rdi+2592]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+50], rax
	mov rax, QWORD PTR [rdi+2600]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+42], rax
	mov rax, QWORD PTR [rdi+2608]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+34], rax
	mov rax, QWORD PTR [rdi+2616]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+26], rax
	mov rax, QWORD PTR [rdi+2624]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+18], rax
	mov rax, QWORD PTR [rdi+2632]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+10], rax
	mov rax, QWORD PTR [rdi+2640]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+2], rax
	mov rax, QWORD PTR [rdi+2648]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsi], dl
	mov rdx, rax
	mov BYTE PTR [rsi+1], dl
	mov rax, rcx
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_ecdh_p521_adx:
	mov r8, rcx
	mov r9, rdx
	mov rcx, rsi
	add rdx, 1
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r14, rdi
	mov rdi, r8
	mov rax, QWORD PTR [rcx+58]
	bswap rax
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rcx+50]
	bswap rax
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rcx+42]
	bswap rax
	mov QWORD PTR [rdi+2312], rax
	mov rax, QWORD PTR [rcx+34]
	bswap rax
	mov QWORD PTR [rdi+2320], rax
	mov rax, QWORD PTR [rcx+26]
	bswap rax
	mov QWORD PTR [rdi+2328], rax
	mov rax, QWORD PTR [rcx+18]
	bswap rax
	mov QWORD PTR [rdi+2336], rax
	mov rax, QWORD PTR [rcx+10]
	bswap rax
	mov QWORD PTR [rdi+2344], rax
	mov rax, QWORD PTR [rcx+2]
	bswap rax
	mov QWORD PTR [rdi+2352], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2360], rax
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2368], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2376], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2384], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2392], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2400], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2408], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2416], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2424], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2432], rax
	mov rax, QWORD PTR [rdx+58]
	bswap rax
	mov QWORD PTR [rdi+2440], rax
	mov rax, QWORD PTR [rdx+50]
	bswap rax
	mov QWORD PTR [rdi+2448], rax
	mov rax, QWORD PTR [rdx+42]
	bswap rax
	mov QWORD PTR [rdi+2456], rax
	mov rax, QWORD PTR [rdx+34]
	bswap rax
	mov QWORD PTR [rdi+2464], rax
	mov rax, QWORD PTR [rdx+26]
	bswap rax
	mov QWORD PTR [rdi+2472], rax
	mov rax, QWORD PTR [rdx+18]
	bswap rax
	mov QWORD PTR [rdi+2480], rax
	mov rax, QWORD PTR [rdx+10]
	bswap rax
	mov QWORD PTR [rdi+2488], rax
	mov rax, QWORD PTR [rdx+2]
	bswap rax
	mov QWORD PTR [rdi+2496], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2504], rax
	movabs rax, -1
	mov QWORD PTR [rdi+64], rax
	movabs rax, -1
	mov QWORD PTR [rdi+72], rax
	movabs rax, -1
	mov QWORD PTR [rdi+80], rax
	movabs rax, -1
	mov QWORD PTR [rdi+88], rax
	movabs rax, -1
	mov QWORD PTR [rdi+96], rax
	movabs rax, -1
	mov QWORD PTR [rdi+104], rax
	movabs rax, -1
	mov QWORD PTR [rdi+112], rax
	movabs rax, -1
	mov QWORD PTR [rdi+120], rax
	movabs rax, 511
	mov QWORD PTR [rdi+128], rax
	movabs rax, -4940528924288850935
	mov QWORD PTR [rdi+136], rax
	movabs rax, 4302566813442262958
	mov QWORD PTR [rdi+144], rax
	movabs rax, 9208736750959699408
	mov QWORD PTR [rdi+152], rax
	movabs rax, 5874531763869423211
	mov QWORD PTR [rdi+160], rax
	movabs rax, -6
	mov QWORD PTR [rdi+168], rax
	movabs rax, -1
	mov QWORD PTR [rdi+176], rax
	movabs rax, -1
	mov QWORD PTR [rdi+184], rax
	movabs rax, -1
	mov QWORD PTR [rdi+192], rax
	movabs rax, 511
	mov QWORD PTR [rdi+200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+280], rax
	movabs rax, 0
	mov QWORD PTR [rdi+288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+296], rax
	movabs rax, 0
	mov QWORD PTR [rdi+304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+344], rax
	movabs rax, 1
	mov QWORD PTR [rdi+352], rax
	movabs rax, 0
	mov QWORD PTR [rdi+360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+416], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+488], rax
	movabs rax, -108086391056891905
	mov QWORD PTR [rdi+496], rax
	movabs rax, -1
	mov QWORD PTR [rdi+504], rax
	movabs rax, -1
	mov QWORD PTR [rdi+512], rax
	movabs rax, -1
	mov QWORD PTR [rdi+520], rax
	movabs rax, -1
	mov QWORD PTR [rdi+528], rax
	movabs rax, -1
	mov QWORD PTR [rdi+536], rax
	movabs rax, -1
	mov QWORD PTR [rdi+544], rax
	movabs rax, -1
	mov QWORD PTR [rdi+552], rax
	movabs rax, 511
	mov QWORD PTR [rdi+560], rax
	movabs rax, -9206149359546586475
	mov QWORD PTR [rdi+568], rax
	movabs rax, 7703098954667325534
	mov QWORD PTR [rdi+576], rax
	movabs rax, -8444198932957117873
	mov QWORD PTR [rdi+584], rax
	movabs rax, 4080679219017386654
	mov QWORD PTR [rdi+592], rax
	movabs rax, -3314326249800548899
	mov QWORD PTR [rdi+600], rax
	movabs rax, -1327138235749078642
	mov QWORD PTR [rdi+608], rax
	movabs rax, 7346575694218300576
	mov QWORD PTR [rdi+616], rax
	movabs rax, 3412575346494654433
	mov QWORD PTR [rdi+624], rax
	movabs rax, 231
	mov QWORD PTR [rdi+632], rax
	movabs rax, -5534465018312146687
	mov QWORD PTR [rdi+640], rax
	movabs rax, 5619576712772809438
	mov QWORD PTR [rdi+648], rax
	movabs rax, 8005610518557668641
	mov QWORD PTR [rdi+656], rax
	movabs rax, -7746456476338520108
	mov QWORD PTR [rdi+664], rax
	movabs rax, -2499315621146659924
	mov QWORD PTR [rdi+672], rax
	movabs rax, -7999496471265827170
	mov QWORD PTR [rdi+680], rax
	movabs rax, 2399910904520155098
	mov QWORD PTR [rdi+688], rax
	movabs rax, -1815197603150574886
	mov QWORD PTR [rdi+696], rax
	movabs rax, 116
	mov QWORD PTR [rdi+704], rax
	movabs rax, 2902022722397546126
	mov QWORD PTR [rdi+712], rax
	movabs rax, 2325088080057329843
	mov QWORD PTR [rdi+720], rax
	movabs rax, -5721086412136040095
	mov QWORD PTR [rdi+728], rax
	movabs rax, 2333612672179754627
	mov QWORD PTR [rdi+736], rax
	movabs rax, 1606649517559478803
	mov QWORD PTR [rdi+744], rax
	movabs rax, 3750328465540489011
	mov QWORD PTR [rdi+752], rax
	movabs rax, -1383596148691055198
	mov QWORD PTR [rdi+760], rax
	movabs rax, 157139108829216397
	mov QWORD PTR [rdi+768], rax
	movabs rax, 480
	mov QWORD PTR [rdi+776], rax
	movabs rax, 1404226216438127876
	mov QWORD PTR [rdi+784], rax
	movabs rax, -646342563601285469
	mov QWORD PTR [rdi+792], rax
	movabs rax, 1344198287485662207
	mov QWORD PTR [rdi+800], rax
	movabs rax, -3210469545270092282
	mov QWORD PTR [rdi+808], rax
	movabs rax, -2491014132492810277
	mov QWORD PTR [rdi+816], rax
	movabs rax, -3462193604041806274
	mov QWORD PTR [rdi+824], rax
	movabs rax, 6614782218913277884
	mov QWORD PTR [rdi+832], rax
	movabs rax, 3282565375810407749
	mov QWORD PTR [rdi+840], rax
	movabs rax, 61
	mov QWORD PTR [rdi+848], rax
	movabs rax, -324259173170675712
	mov QWORD PTR [rdi+856], rax
	movabs rax, 2927982029091333069
	mov QWORD PTR [rdi+864], rax
	movabs rax, 1720978806102766044
	mov QWORD PTR [rdi+872], rax
	movabs rax, -3873067094995862739
	mov QWORD PTR [rdi+880], rax
	movabs rax, 204699087262476340
	mov QWORD PTR [rdi+888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+896], rax
	movabs rax, 0
	mov QWORD PTR [rdi+904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+920], rax
	movabs rax, -3
	mov QWORD PTR [rdi+928], rax
	movabs rax, -1
	mov QWORD PTR [rdi+936], rax
	movabs rax, -1
	mov QWORD PTR [rdi+944], rax
	movabs rax, -1
	mov QWORD PTR [rdi+952], rax
	movabs rax, -1
	mov QWORD PTR [rdi+960], rax
	movabs rax, -1
	mov QWORD PTR [rdi+968], rax
	movabs rax, -1
	mov QWORD PTR [rdi+976], rax
	movabs rax, -1
	mov QWORD PTR [rdi+984], rax
	movabs rax, 511
	mov QWORD PTR [rdi+992], rax
	movabs rax, -4940528924288850937
	mov QWORD PTR [rdi+1000], rax
	movabs rax, 4302566813442262958
	mov QWORD PTR [rdi+1008], rax
	movabs rax, 9208736750959699408
	mov QWORD PTR [rdi+1016], rax
	movabs rax, 5874531763869423211
	mov QWORD PTR [rdi+1024], rax
	movabs rax, -6
	mov QWORD PTR [rdi+1032], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1040], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1048], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1056], rax
	movabs rax, 511
	mov QWORD PTR [rdi+1064], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1080], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1088], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1104], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1112], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1184], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1248], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1280], rax
	movabs rax, -1
	mov QWORD PTR [rdi+3232], rax
	mov rsi, r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+2296]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3304], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3305], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3306], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3307], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3308], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3309], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3310], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3311], dl
	add rbx, 1
	cmp rbx, 72
	jne 20b
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rdi+rbx*1+928]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3888], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3889], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3890], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3891], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3892], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3893], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3894], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3895], dl
	add rbx, 1
	cmp rbx, 72
	jne 21b
	mov ebx, 0
22:
	movzx eax, BYTE PTR [rdi+rbx*1+1000]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4472], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4473], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4474], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4475], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4476], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4477], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4478], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4479], dl
	add rbx, 1
	cmp rbx, 72
	jne 22b
	movabs rax, 0
	mov QWORD PTR [rdi+2872], rax
	movabs rax, 70368744177664
	mov QWORD PTR [rdi+2880], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2896], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2920], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2928], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2936], rax
	movabs rax, -9217631144418712697
	mov QWORD PTR [rdi+2944], rax
	movabs rax, 8716614342792292383
	mov QWORD PTR [rdi+2952], rax
	movabs rax, -8963647668888889830
	mov QWORD PTR [rdi+2960], rax
	movabs rax, -4788688284897388321
	mov QWORD PTR [rdi+2968], rax
	movabs rax, -1104775416600182967
	mov QWORD PTR [rdi+2976], rax
	movabs rax, -442379411916359548
	mov QWORD PTR [rdi+2984], rax
	movabs rax, 8597773255975950730
	mov QWORD PTR [rdi+2992], rax
	movabs rax, 1137525115498218144
	mov QWORD PTR [rdi+3000], rax
	movabs rax, 77
	mov QWORD PTR [rdi+3008], rax
	mov rdx, r9
	add rdx, 67
	mov rax, QWORD PTR [rdx+58]
	bswap rax
	mov QWORD PTR [rdi+2656], rax
	mov rax, QWORD PTR [rdx+50]
	bswap rax
	mov QWORD PTR [rdi+2664], rax
	mov rax, QWORD PTR [rdx+42]
	bswap rax
	mov QWORD PTR [rdi+2672], rax
	mov rax, QWORD PTR [rdx+34]
	bswap rax
	mov QWORD PTR [rdi+2680], rax
	mov rax, QWORD PTR [rdx+26]
	bswap rax
	mov QWORD PTR [rdi+2688], rax
	mov rax, QWORD PTR [rdx+18]
	bswap rax
	mov QWORD PTR [rdi+2696], rax
	mov rax, QWORD PTR [rdx+10]
	bswap rax
	mov QWORD PTR [rdi+2704], rax
	mov rax, QWORD PTR [rdx+2]
	bswap rax
	mov QWORD PTR [rdi+2712], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2720], rax
	movzx edx, BYTE PTR [r9]
	xor rdx, 4
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	call {vg_p521_check_point_adx}
	mov r8, QWORD PTR [rdi+2360]
	and r8, 511
	mov QWORD PTR [rdi+2360], r8
	movabs rax, -8608480567731124088
	mov QWORD PTR [rdi+5176], rax
	movabs rax, -8608480567731124088
	mov QWORD PTR [rdi+5184], rax
	movabs rax, -8608480567731124088
	mov QWORD PTR [rdi+5192], rax
	movabs rax, -8608480567731124088
	mov QWORD PTR [rdi+5200], rax
	movabs rax, -8608480567731124088
	mov QWORD PTR [rdi+5208], rax
	movabs rax, -8608480567731124088
	mov QWORD PTR [rdi+5216], rax
	movabs rax, -8608480567731124088
	mov QWORD PTR [rdi+5224], rax
	movabs rax, -8608480567731124088
	mov QWORD PTR [rdi+5232], rax
	movabs rax, 2184
	mov QWORD PTR [rdi+5240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5248], rax
	mov r8, QWORD PTR [rdi+5176]
	add r8, QWORD PTR [rdi+2296]
	mov QWORD PTR [rdi+5176], r8
	mov r8, QWORD PTR [rdi+5184]
	adc r8, QWORD PTR [rdi+2304]
	mov QWORD PTR [rdi+5184], r8
	mov r8, QWORD PTR [rdi+5192]
	adc r8, QWORD PTR [rdi+2312]
	mov QWORD PTR [rdi+5192], r8
	mov r8, QWORD PTR [rdi+5200]
	adc r8, QWORD PTR [rdi+2320]
	mov QWORD PTR [rdi+5200], r8
	mov r8, QWORD PTR [rdi+5208]
	adc r8, QWORD PTR [rdi+2328]
	mov QWORD PTR [rdi+5208], r8
	mov r8, QWORD PTR [rdi+5216]
	adc r8, QWORD PTR [rdi+2336]
	mov QWORD PTR [rdi+5216], r8
	mov r8, QWORD PTR [rdi+5224]
	adc r8, QWORD PTR [rdi+2344]
	mov QWORD PTR [rdi+5224], r8
	mov r8, QWORD PTR [rdi+5232]
	adc r8, QWORD PTR [rdi+2352]
	mov QWORD PTR [rdi+5232], r8
	mov r8, QWORD PTR [rdi+5240]
	adc r8, QWORD PTR [rdi+2360]
	mov QWORD PTR [rdi+5240], r8
	mov r8, QWORD PTR [rdi+5248]
	adc r8, 0
	mov QWORD PTR [rdi+5248], r8
	mov ebx, 0
23:
	movzx eax, BYTE PTR [rdi+rbx*1+5176]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+5320], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+5321], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+5322], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+5323], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+5324], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+5325], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+5326], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+5327], dl
	add rbx, 1
	cmp rbx, 80
	jne 23b
	mov rax, QWORD PTR [rdi+2800]
	mov QWORD PTR [rdi+6112], rax
	mov rax, QWORD PTR [rdi+2808]
	mov QWORD PTR [rdi+6120], rax
	mov rax, QWORD PTR [rdi+2816]
	mov QWORD PTR [rdi+6128], rax
	mov rax, QWORD PTR [rdi+2824]
	mov QWORD PTR [rdi+6136], rax
	mov rax, QWORD PTR [rdi+2832]
	mov QWORD PTR [rdi+6144], rax
	mov rax, QWORD PTR [rdi+2840]
	mov QWORD PTR [rdi+6152], rax
	mov rax, QWORD PTR [rdi+2848]
	mov QWORD PTR [rdi+6160], rax
	mov rax, QWORD PTR [rdi+2856]
	mov QWORD PTR [rdi+6168], rax
	mov rax, QWORD PTR [rdi+2864]
	mov QWORD PTR [rdi+6176], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+6184], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+6192], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+6200], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+6208], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+6216], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+6224], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+6232], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+6240], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+6248], rax
	mov rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+6256], rax
	mov rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+6264], rax
	mov rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+6272], rax
	mov rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+6280], rax
	mov rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+6288], rax
	mov rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+6296], rax
	mov rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+6304], rax
	mov rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+6312], rax
	mov rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+6320], rax
	mov rax, QWORD PTR [rdi+2800]
	mov QWORD PTR [rdi+1504], rax
	mov rax, QWORD PTR [rdi+2808]
	mov QWORD PTR [rdi+1512], rax
	mov rax, QWORD PTR [rdi+2816]
	mov QWORD PTR [rdi+1520], rax
	mov rax, QWORD PTR [rdi+2824]
	mov QWORD PTR [rdi+1528], rax
	mov rax, QWORD PTR [rdi+2832]
	mov QWORD PTR [rdi+1536], rax
	mov rax, QWORD PTR [rdi+2840]
	mov QWORD PTR [rdi+1544], rax
	mov rax, QWORD PTR [rdi+2848]
	mov QWORD PTR [rdi+1552], rax
	mov rax, QWORD PTR [rdi+2856]
	mov QWORD PTR [rdi+1560], rax
	mov rax, QWORD PTR [rdi+2864]
	mov QWORD PTR [rdi+1568], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+1600], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+1608], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+1616], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+1624], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+1632], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+1640], rax
	mov rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+1648], rax
	mov rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+1656], rax
	mov rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+1664], rax
	mov rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+1672], rax
	mov rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+1680], rax
	mov rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+1688], rax
	mov rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+1696], rax
	mov rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+1704], rax
	mov rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+1712], rax
	mov ebx, 7
24:
	sub rbx, 1
	mov r12, rsi
	mov esi, 1720
	mov edx, 1504
	mov ecx, 2800
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1576
	mov ecx, 3160
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1648
	mov ecx, 424
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1504
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 2800
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -1152
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 2008
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1576
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	add rdi, 3160
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -2736
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 864
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 2008
	mov edx, 2008
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 2008
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -720
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 720
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	add rdi, 1504
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 2800
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -2376
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 936
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1288
	mov edx, 1288
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1432
	mov edx, 2944
	mov ecx, 1864
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 144
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -504
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1360
	mov edx, 2944
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, -72
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 432
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -432
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 72
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1720
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1720
	mov r12, rsi
	mov esi, 1792
	mov edx, 2008
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1720
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1360
	mov edx, 1288
	mov ecx, 1432
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1432
	mov edx, 2008
	mov ecx, 1432
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1936
	mov ecx, 1720
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+1504], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+1512], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+1520], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+1528], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+1536], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+1544], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+1552], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+1560], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+1568], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+1600], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+1608], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+1616], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+1624], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+1632], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+1640], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+1648], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+1656], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+1664], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+1672], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+1680], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+1688], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+1696], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+1704], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+1712], rax
	cmp rbx, 6
	je 25f
	cmp rbx, 5
	je 27f
	cmp rbx, 4
	je 29f
	cmp rbx, 3
	je 211f
	cmp rbx, 2
	je 213f
	cmp rbx, 1
	je 215f
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+7624], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+7632], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+7640], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+7648], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+7656], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+7664], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+7672], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+7680], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+7688], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7696], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7704], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7712], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7720], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7728], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7736], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7744], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7752], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7760], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+7768], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+7776], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+7784], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+7792], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+7800], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+7808], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+7816], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+7824], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+7832], rax
	jmp 216f
215:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+7408], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+7416], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+7424], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+7432], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+7440], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+7448], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+7456], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+7464], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+7472], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7480], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7488], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7496], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7504], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7512], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7520], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7528], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7536], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7544], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+7552], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+7560], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+7568], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+7576], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+7584], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+7592], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+7600], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+7608], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+7616], rax
216:
	jmp 214f
213:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+7192], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+7200], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+7208], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+7216], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+7224], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+7232], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+7240], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+7248], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+7256], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7264], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7272], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7280], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7288], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7296], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7304], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7312], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7320], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7328], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+7336], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+7344], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+7352], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+7360], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+7368], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+7376], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+7384], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+7392], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+7400], rax
214:
	jmp 212f
211:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+6976], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+6984], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+6992], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+7000], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+7008], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+7016], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+7024], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+7032], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+7040], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7048], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7056], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7064], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7072], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7080], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7088], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7096], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7104], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7112], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+7120], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+7128], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+7136], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+7144], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+7152], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+7160], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+7168], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+7176], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+7184], rax
212:
	jmp 210f
29:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+6760], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+6768], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+6776], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+6784], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+6792], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+6800], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+6808], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+6816], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+6824], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6832], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6840], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6848], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6856], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6864], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6872], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6880], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6888], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6896], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+6904], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+6912], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+6920], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+6928], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+6936], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+6944], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+6952], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+6960], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+6968], rax
210:
	jmp 28f
27:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+6544], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+6552], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+6560], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+6568], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+6576], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+6584], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+6592], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+6600], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+6608], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6616], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6624], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6632], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6640], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6648], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6656], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6664], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6672], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6680], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+6688], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+6696], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+6704], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+6712], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+6720], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+6728], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+6736], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+6744], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+6752], rax
28:
	jmp 26f
25:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+6328], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+6336], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+6344], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+6352], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+6360], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+6368], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+6376], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+6384], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+6392], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6400], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6408], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6416], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6424], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6432], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6440], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6448], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6456], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6464], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+6472], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+6480], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+6488], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+6496], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+6504], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+6512], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+6520], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+6528], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+6536], rax
26:
	test rbx, rbx
	jne 24b
	mov rax, QWORD PTR [rdi+6256]
	mov QWORD PTR [rdi+1432], rax
	mov rax, QWORD PTR [rdi+6264]
	mov QWORD PTR [rdi+1440], rax
	mov rax, QWORD PTR [rdi+6272]
	mov QWORD PTR [rdi+1448], rax
	mov rax, QWORD PTR [rdi+6280]
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+6288]
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+6296]
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+6304]
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+6312]
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+6320]
	mov QWORD PTR [rdi+1496], rax
	mov rax, QWORD PTR [rdi+6472]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6480]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6488]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6496]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6504]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6512]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6520]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6528]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6536]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1720
	mov edx, 1432
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6688]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6696]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6704]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6712]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6720]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6728]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6736]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6744]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6752]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1792
	mov edx, 1720
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6904]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6912]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6920]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6928]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6936]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6944]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6952]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6960]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6968]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1864
	mov edx, 1792
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7120]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7128]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7136]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7144]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7152]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7160]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7168]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7176]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7184]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1936
	mov edx, 1864
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7336]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7344]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7352]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7360]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7368]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7376]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7384]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7392]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7400]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 2008
	mov edx, 1936
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7552]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7560]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7568]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7576]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7584]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7592]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7600]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7608]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7616]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 2080
	mov edx, 2008
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7768]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7776]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7784]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7792]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7800]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7808]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7816]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7824]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7832]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1216
	mov edx, 2080
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+5320]
	mov QWORD PTR [rdi+4472], rax
	mov rax, QWORD PTR [rdi+5328]
	mov QWORD PTR [rdi+4480], rax
	mov rax, QWORD PTR [rdi+5336]
	mov QWORD PTR [rdi+4488], rax
	mov rax, QWORD PTR [rdi+5344]
	mov QWORD PTR [rdi+4496], rax
	mov rax, QWORD PTR [rdi+5352]
	mov QWORD PTR [rdi+4504], rax
	mov rax, QWORD PTR [rdi+5360]
	mov QWORD PTR [rdi+4512], rax
	mov rax, QWORD PTR [rdi+5368]
	mov QWORD PTR [rdi+4520], rax
	mov rax, QWORD PTR [rdi+5376]
	mov QWORD PTR [rdi+4528], rax
	mov rax, QWORD PTR [rdi+5384]
	mov QWORD PTR [rdi+4536], rax
	mov rax, QWORD PTR [rdi+5392]
	mov QWORD PTR [rdi+4544], rax
	mov rax, QWORD PTR [rdi+5400]
	mov QWORD PTR [rdi+4552], rax
	mov rax, QWORD PTR [rdi+5408]
	mov QWORD PTR [rdi+4560], rax
	mov rax, QWORD PTR [rdi+5416]
	mov QWORD PTR [rdi+4568], rax
	mov rax, QWORD PTR [rdi+5424]
	mov QWORD PTR [rdi+4576], rax
	mov rax, QWORD PTR [rdi+5432]
	mov QWORD PTR [rdi+4584], rax
	mov rax, QWORD PTR [rdi+5440]
	mov QWORD PTR [rdi+4592], rax
	mov rax, QWORD PTR [rdi+5448]
	mov QWORD PTR [rdi+4600], rax
	mov rax, QWORD PTR [rdi+5456]
	mov QWORD PTR [rdi+4608], rax
	mov rax, QWORD PTR [rdi+5464]
	mov QWORD PTR [rdi+4616], rax
	mov rax, QWORD PTR [rdi+5472]
	mov QWORD PTR [rdi+4624], rax
	mov rax, QWORD PTR [rdi+5480]
	mov QWORD PTR [rdi+4632], rax
	mov rax, QWORD PTR [rdi+5488]
	mov QWORD PTR [rdi+4640], rax
	mov rax, QWORD PTR [rdi+5496]
	mov QWORD PTR [rdi+4648], rax
	mov rax, QWORD PTR [rdi+5504]
	mov QWORD PTR [rdi+4656], rax
	mov rax, QWORD PTR [rdi+5512]
	mov QWORD PTR [rdi+4664], rax
	mov rax, QWORD PTR [rdi+5520]
	mov QWORD PTR [rdi+4672], rax
	mov rax, QWORD PTR [rdi+5528]
	mov QWORD PTR [rdi+4680], rax
	mov rax, QWORD PTR [rdi+5536]
	mov QWORD PTR [rdi+4688], rax
	mov rax, QWORD PTR [rdi+5544]
	mov QWORD PTR [rdi+4696], rax
	mov rax, QWORD PTR [rdi+5552]
	mov QWORD PTR [rdi+4704], rax
	mov rax, QWORD PTR [rdi+5560]
	mov QWORD PTR [rdi+4712], rax
	mov rax, QWORD PTR [rdi+5568]
	mov QWORD PTR [rdi+4720], rax
	mov rax, QWORD PTR [rdi+5576]
	mov QWORD PTR [rdi+4728], rax
	mov rax, QWORD PTR [rdi+5584]
	mov QWORD PTR [rdi+4736], rax
	mov rax, QWORD PTR [rdi+5592]
	mov QWORD PTR [rdi+4744], rax
	mov rax, QWORD PTR [rdi+5600]
	mov QWORD PTR [rdi+4752], rax
	mov rax, QWORD PTR [rdi+5608]
	mov QWORD PTR [rdi+4760], rax
	mov rax, QWORD PTR [rdi+5616]
	mov QWORD PTR [rdi+4768], rax
	mov rax, QWORD PTR [rdi+5624]
	mov QWORD PTR [rdi+4776], rax
	mov rax, QWORD PTR [rdi+5632]
	mov QWORD PTR [rdi+4784], rax
	mov rax, QWORD PTR [rdi+5640]
	mov QWORD PTR [rdi+4792], rax
	mov rax, QWORD PTR [rdi+5648]
	mov QWORD PTR [rdi+4800], rax
	mov rax, QWORD PTR [rdi+5656]
	mov QWORD PTR [rdi+4808], rax
	mov rax, QWORD PTR [rdi+5664]
	mov QWORD PTR [rdi+4816], rax
	mov rax, QWORD PTR [rdi+5672]
	mov QWORD PTR [rdi+4824], rax
	mov rax, QWORD PTR [rdi+5680]
	mov QWORD PTR [rdi+4832], rax
	mov rax, QWORD PTR [rdi+5688]
	mov QWORD PTR [rdi+4840], rax
	mov rax, QWORD PTR [rdi+2224]
	mov QWORD PTR [rdi+4848], rax
	mov rax, QWORD PTR [rdi+2232]
	mov QWORD PTR [rdi+4856], rax
	mov rax, QWORD PTR [rdi+2240]
	mov QWORD PTR [rdi+4864], rax
	mov rax, QWORD PTR [rdi+2248]
	mov QWORD PTR [rdi+4872], rax
	mov rax, QWORD PTR [rdi+2256]
	mov QWORD PTR [rdi+4880], rax
	mov rax, QWORD PTR [rdi+2264]
	mov QWORD PTR [rdi+4888], rax
	mov rax, QWORD PTR [rdi+2272]
	mov QWORD PTR [rdi+4896], rax
	mov rax, QWORD PTR [rdi+2280]
	mov QWORD PTR [rdi+4904], rax
	mov rax, QWORD PTR [rdi+2288]
	mov QWORD PTR [rdi+4912], rax
	call {vg_p521_inv_mod_p}
	mov rax, QWORD PTR [rdi+2152]
	mov QWORD PTR [rdi+1504], rax
	mov rax, QWORD PTR [rdi+2160]
	mov QWORD PTR [rdi+1512], rax
	mov rax, QWORD PTR [rdi+2168]
	mov QWORD PTR [rdi+1520], rax
	mov rax, QWORD PTR [rdi+2176]
	mov QWORD PTR [rdi+1528], rax
	mov rax, QWORD PTR [rdi+2184]
	mov QWORD PTR [rdi+1536], rax
	mov rax, QWORD PTR [rdi+2192]
	mov QWORD PTR [rdi+1544], rax
	mov rax, QWORD PTR [rdi+2200]
	mov QWORD PTR [rdi+1552], rax
	mov rax, QWORD PTR [rdi+2208]
	mov QWORD PTR [rdi+1560], rax
	mov rax, QWORD PTR [rdi+2216]
	mov QWORD PTR [rdi+1568], rax
	mov rax, QWORD PTR [rdi+4848]
	mov QWORD PTR [rdi+2224], rax
	mov rax, QWORD PTR [rdi+4856]
	mov QWORD PTR [rdi+2232], rax
	mov rax, QWORD PTR [rdi+4864]
	mov QWORD PTR [rdi+2240], rax
	mov rax, QWORD PTR [rdi+4872]
	mov QWORD PTR [rdi+2248], rax
	mov rax, QWORD PTR [rdi+4880]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rdi+4888]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rdi+4896]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rdi+4904]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rdi+4912]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rdi+4472]
	mov QWORD PTR [rdi+5320], rax
	mov rax, QWORD PTR [rdi+4480]
	mov QWORD PTR [rdi+5328], rax
	mov rax, QWORD PTR [rdi+4488]
	mov QWORD PTR [rdi+5336], rax
	mov rax, QWORD PTR [rdi+4496]
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+4504]
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+4512]
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+4520]
	mov QWORD PTR [rdi+5368], rax
	mov rax, QWORD PTR [rdi+4528]
	mov QWORD PTR [rdi+5376], rax
	mov rax, QWORD PTR [rdi+4536]
	mov QWORD PTR [rdi+5384], rax
	mov rax, QWORD PTR [rdi+4544]
	mov QWORD PTR [rdi+5392], rax
	mov rax, QWORD PTR [rdi+4552]
	mov QWORD PTR [rdi+5400], rax
	mov rax, QWORD PTR [rdi+4560]
	mov QWORD PTR [rdi+5408], rax
	mov rax, QWORD PTR [rdi+4568]
	mov QWORD PTR [rdi+5416], rax
	mov rax, QWORD PTR [rdi+4576]
	mov QWORD PTR [rdi+5424], rax
	mov rax, QWORD PTR [rdi+4584]
	mov QWORD PTR [rdi+5432], rax
	mov rax, QWORD PTR [rdi+4592]
	mov QWORD PTR [rdi+5440], rax
	mov rax, QWORD PTR [rdi+4600]
	mov QWORD PTR [rdi+5448], rax
	mov rax, QWORD PTR [rdi+4608]
	mov QWORD PTR [rdi+5456], rax
	mov rax, QWORD PTR [rdi+4616]
	mov QWORD PTR [rdi+5464], rax
	mov rax, QWORD PTR [rdi+4624]
	mov QWORD PTR [rdi+5472], rax
	mov rax, QWORD PTR [rdi+4632]
	mov QWORD PTR [rdi+5480], rax
	mov rax, QWORD PTR [rdi+4640]
	mov QWORD PTR [rdi+5488], rax
	mov rax, QWORD PTR [rdi+4648]
	mov QWORD PTR [rdi+5496], rax
	mov rax, QWORD PTR [rdi+4656]
	mov QWORD PTR [rdi+5504], rax
	mov rax, QWORD PTR [rdi+4664]
	mov QWORD PTR [rdi+5512], rax
	mov rax, QWORD PTR [rdi+4672]
	mov QWORD PTR [rdi+5520], rax
	mov rax, QWORD PTR [rdi+4680]
	mov QWORD PTR [rdi+5528], rax
	mov rax, QWORD PTR [rdi+4688]
	mov QWORD PTR [rdi+5536], rax
	mov rax, QWORD PTR [rdi+4696]
	mov QWORD PTR [rdi+5544], rax
	mov rax, QWORD PTR [rdi+4704]
	mov QWORD PTR [rdi+5552], rax
	mov rax, QWORD PTR [rdi+4712]
	mov QWORD PTR [rdi+5560], rax
	mov rax, QWORD PTR [rdi+4720]
	mov QWORD PTR [rdi+5568], rax
	mov rax, QWORD PTR [rdi+4728]
	mov QWORD PTR [rdi+5576], rax
	mov rax, QWORD PTR [rdi+4736]
	mov QWORD PTR [rdi+5584], rax
	mov rax, QWORD PTR [rdi+4744]
	mov QWORD PTR [rdi+5592], rax
	mov rax, QWORD PTR [rdi+4752]
	mov QWORD PTR [rdi+5600], rax
	mov rax, QWORD PTR [rdi+4760]
	mov QWORD PTR [rdi+5608], rax
	mov rax, QWORD PTR [rdi+4768]
	mov QWORD PTR [rdi+5616], rax
	mov rax, QWORD PTR [rdi+4776]
	mov QWORD PTR [rdi+5624], rax
	mov rax, QWORD PTR [rdi+4784]
	mov QWORD PTR [rdi+5632], rax
	mov rax, QWORD PTR [rdi+4792]
	mov QWORD PTR [rdi+5640], rax
	mov rax, QWORD PTR [rdi+4800]
	mov QWORD PTR [rdi+5648], rax
	mov rax, QWORD PTR [rdi+4808]
	mov QWORD PTR [rdi+5656], rax
	mov rax, QWORD PTR [rdi+4816]
	mov QWORD PTR [rdi+5664], rax
	mov rax, QWORD PTR [rdi+4824]
	mov QWORD PTR [rdi+5672], rax
	mov rax, QWORD PTR [rdi+4832]
	mov QWORD PTR [rdi+5680], rax
	mov rax, QWORD PTR [rdi+4840]
	mov QWORD PTR [rdi+5688], rax
	mov r12, rsi
	mov esi, 1288
	mov edx, 1504
	mov ecx, 2080
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7768]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7776]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7784]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7792]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7800]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7808]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7816]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7824]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7832]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1504
	mov edx, 1504
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7624]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7632]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7640]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7648]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7656]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7664]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7672]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7680]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7688]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7624], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7632], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7640], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7648], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7656], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7664], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7672], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7680], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7688], rax
	mov rax, QWORD PTR [rdi+7696]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7704]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7712]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7720]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7728]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7736]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7744]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7752]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7760]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7696], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7704], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7712], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7720], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7728], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7736], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7744], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7752], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7760], rax
	mov r12, rsi
	mov esi, 1288
	mov edx, 1504
	mov ecx, 2008
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7552]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7560]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7568]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7576]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7584]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7592]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7600]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7608]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7616]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1504
	mov edx, 1504
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7408]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7416]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7424]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7432]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7440]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7448]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7456]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7464]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7472]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7408], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7416], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7424], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7432], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7440], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7448], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7456], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7464], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7472], rax
	mov rax, QWORD PTR [rdi+7480]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7488]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7496]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7504]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7512]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7520]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7528]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7536]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7544]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7480], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7488], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7496], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7504], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7512], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7520], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7528], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7536], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7544], rax
	mov r12, rsi
	mov esi, 1288
	mov edx, 1504
	mov ecx, 1936
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7336]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7344]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7352]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7360]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7368]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7376]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7384]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7392]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7400]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1504
	mov edx, 1504
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7192]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7200]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7208]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7216]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7224]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7232]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7240]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7248]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7256]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7192], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7200], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7208], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7216], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7224], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7232], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7240], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7248], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7256], rax
	mov rax, QWORD PTR [rdi+7264]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7272]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7280]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7288]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7296]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7304]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7312]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7320]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7328]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7264], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7272], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7280], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7288], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7296], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7304], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7312], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7320], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7328], rax
	mov r12, rsi
	mov esi, 1288
	mov edx, 1504
	mov ecx, 1864
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+7120]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7128]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7136]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7144]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7152]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7160]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7168]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7176]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7184]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1504
	mov edx, 1504
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6976]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6984]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6992]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7000]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7008]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7016]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7024]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7032]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7040]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6976], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6984], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6992], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7000], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7008], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7016], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7024], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7032], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7040], rax
	mov rax, QWORD PTR [rdi+7048]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7056]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7064]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7072]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7080]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7088]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7096]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7104]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7112]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+7048], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+7056], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+7064], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+7072], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+7080], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+7088], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+7096], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+7104], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+7112], rax
	mov r12, rsi
	mov esi, 1288
	mov edx, 1504
	mov ecx, 1792
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6904]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6912]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6920]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6928]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6936]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6944]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6952]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6960]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6968]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1504
	mov edx, 1504
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6760]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6768]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6776]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6784]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6792]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6800]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6808]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6816]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6824]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6760], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6768], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6776], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6784], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6792], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6800], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6808], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6816], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6824], rax
	mov rax, QWORD PTR [rdi+6832]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6840]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6848]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6856]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6864]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6872]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6880]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6888]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6896]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6832], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6840], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6848], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6856], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6864], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6872], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6880], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6888], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6896], rax
	mov r12, rsi
	mov esi, 1288
	mov edx, 1504
	mov ecx, 1720
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6688]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6696]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6704]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6712]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6720]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6728]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6736]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6744]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6752]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1504
	mov edx, 1504
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6544]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6552]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6560]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6568]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6576]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6584]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6592]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6600]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6608]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6544], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6552], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6560], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6568], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6576], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6584], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6592], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6600], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6608], rax
	mov rax, QWORD PTR [rdi+6616]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6624]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6632]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6640]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6648]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6656]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6664]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6672]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6680]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6616], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6624], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6632], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6640], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6648], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6656], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6664], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6672], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6680], rax
	mov r12, rsi
	mov esi, 1288
	mov edx, 1504
	mov ecx, 1432
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6472]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6480]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6488]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6496]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6504]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6512]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6520]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6528]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6536]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1504
	mov edx, 1504
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+6328]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6336]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6344]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6352]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6360]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6368]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6376]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6384]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6392]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6328], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6336], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6344], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6352], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6360], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6368], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6376], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6384], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6392], rax
	mov rax, QWORD PTR [rdi+6400]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6408]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6416]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6424]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6432]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6440]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6448]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6456]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6464]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6400], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6408], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6416], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6424], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6432], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6440], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6448], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6456], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6464], rax
	mov rax, QWORD PTR [rdi+6112]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6120]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6128]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6136]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6144]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6152]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6160]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6168]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6176]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1504
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6112], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6120], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6128], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6136], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6144], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6152], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6160], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6168], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6176], rax
	mov rax, QWORD PTR [rdi+6184]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+6192]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+6200]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+6208]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+6216]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+6224]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+6232]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+6240]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+6248]
	mov QWORD PTR [rdi+1424], rax
	mov r12, rsi
	mov esi, 1360
	mov edx, 1360
	mov ecx, 1504
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+6184], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+6192], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+6200], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+6208], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+6216], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+6224], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+6232], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+6240], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+6248], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+6256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6280], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6296], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6320], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+6472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6488], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6496], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6504], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6512], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6536], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+6688], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6696], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6704], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6712], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6720], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6728], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6736], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6752], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+6904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6920], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6928], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6936], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6944], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6952], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6960], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6968], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+7120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7128], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7136], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7184], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+7336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7344], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7352], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7400], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+7552], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7560], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7576], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7584], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7592], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7600], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7608], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7616], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+7768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7776], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7784], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7792], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7800], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7808], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7816], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1080], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1088], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1104], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1112], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1184], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1248], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1280], rax
	mov ebx, 131
217:
	sub rbx, 1
	mov rbp, QWORD PTR [rdi+1144]
	mov r8, QWORD PTR [rdi+1152]
	mov r9, QWORD PTR [rdi+1160]
	mov r10, QWORD PTR [rdi+1168]
	mov r11, QWORD PTR [rdi+1176]
	mov r12, QWORD PTR [rdi+1184]
	mov r13, QWORD PTR [rdi+1192]
	mov r14, QWORD PTR [rdi+1200]
	mov r15, QWORD PTR [rdi+1208]
	add rbp, QWORD PTR [rdi+1144]
	adc r8, QWORD PTR [rdi+1152]
	adc r9, QWORD PTR [rdi+1160]
	adc r10, QWORD PTR [rdi+1168]
	adc r11, QWORD PTR [rdi+1176]
	adc r12, QWORD PTR [rdi+1184]
	adc r13, QWORD PTR [rdi+1192]
	adc r14, QWORD PTR [rdi+1200]
	adc r15, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+1144], rbp
	mov QWORD PTR [rdi+1152], r8
	mov QWORD PTR [rdi+1160], r9
	mov QWORD PTR [rdi+1168], r10
	mov QWORD PTR [rdi+1176], r11
	mov QWORD PTR [rdi+1184], r12
	mov QWORD PTR [rdi+1192], r13
	mov QWORD PTR [rdi+1200], r14
	mov QWORD PTR [rdi+1208], r15
	add rbx, 8192
218:
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1216
	call {vg_p521_win_sqr_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq rbx, xmm7
	mov rbp, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+1728]
	mov r9, QWORD PTR [rdi+1736]
	mov r10, QWORD PTR [rdi+1744]
	mov r11, QWORD PTR [rdi+1752]
	mov r12, QWORD PTR [rdi+1760]
	mov r13, QWORD PTR [rdi+1768]
	mov r14, QWORD PTR [rdi+1776]
	mov r15, QWORD PTR [rdi+1784]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1072]
	adc r8, QWORD PTR [rdi+1080]
	adc r9, QWORD PTR [rdi+1088]
	adc r10, QWORD PTR [rdi+1096]
	adc r11, QWORD PTR [rdi+1104]
	adc r12, QWORD PTR [rdi+1112]
	adc r13, QWORD PTR [rdi+1120]
	adc r14, QWORD PTR [rdi+1128]
	adc r15, QWORD PTR [rdi+1136]
	add r15, 512
	mov QWORD PTR [rdi+1792], rbp
	mov QWORD PTR [rdi+1800], r8
	mov QWORD PTR [rdi+1808], r9
	mov QWORD PTR [rdi+1816], r10
	mov QWORD PTR [rdi+1824], r11
	mov QWORD PTR [rdi+1832], r12
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1144
	mov rbx, rdi
	add rbx, 1216
	call {vg_p521_win_mul_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1216], rbp
	mov QWORD PTR [rdi+1224], r8
	mov QWORD PTR [rdi+1232], r9
	mov QWORD PTR [rdi+1240], r10
	mov QWORD PTR [rdi+1248], r11
	mov QWORD PTR [rdi+1256], r12
	mov QWORD PTR [rdi+1264], r13
	mov QWORD PTR [rdi+1272], r14
	mov QWORD PTR [rdi+1280], r15
	movq rbx, xmm7
	movq rsi, xmm6
	mov rbp, QWORD PTR [rdi+1072]
	mov r8, QWORD PTR [rdi+1080]
	mov r9, QWORD PTR [rdi+1088]
	mov r10, QWORD PTR [rdi+1096]
	mov r11, QWORD PTR [rdi+1104]
	mov r12, QWORD PTR [rdi+1112]
	mov r13, QWORD PTR [rdi+1120]
	mov r14, QWORD PTR [rdi+1128]
	mov r15, QWORD PTR [rdi+1136]
	add rbp, QWORD PTR [rdi+1720]
	adc r8, QWORD PTR [rdi+1728]
	adc r9, QWORD PTR [rdi+1736]
	adc r10, QWORD PTR [rdi+1744]
	adc r11, QWORD PTR [rdi+1752]
	adc r12, QWORD PTR [rdi+1760]
	adc r13, QWORD PTR [rdi+1768]
	adc r14, QWORD PTR [rdi+1776]
	adc r15, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1792
	mov rbx, rdi
	add rbx, 1720
	call {vg_p521_win_mul_adx}
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq rbx, xmm7
	movq rsi, xmm6
	mov rbp, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+1728]
	mov r9, QWORD PTR [rdi+1736]
	mov r10, QWORD PTR [rdi+1744]
	mov r11, QWORD PTR [rdi+1752]
	mov r12, QWORD PTR [rdi+1760]
	mov r13, QWORD PTR [rdi+1768]
	mov r14, QWORD PTR [rdi+1776]
	mov r15, QWORD PTR [rdi+1784]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	add rbp, QWORD PTR [rdi+1720]
	adc r8, QWORD PTR [rdi+1728]
	adc r9, QWORD PTR [rdi+1736]
	adc r10, QWORD PTR [rdi+1744]
	adc r11, QWORD PTR [rdi+1752]
	adc r12, QWORD PTR [rdi+1760]
	adc r13, QWORD PTR [rdi+1768]
	adc r14, QWORD PTR [rdi+1776]
	adc r15, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1144
	call {vg_p521_win_sqr_adx}
	mov QWORD PTR [rdi+1792], rbp
	mov QWORD PTR [rdi+1800], r8
	mov QWORD PTR [rdi+1808], r9
	mov QWORD PTR [rdi+1816], r10
	mov QWORD PTR [rdi+1824], r11
	mov QWORD PTR [rdi+1832], r12
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	movq rbx, xmm7
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1072
	mov rbx, rdi
	add rbx, 1792
	call {vg_p521_win_mul_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1864], rbp
	mov QWORD PTR [rdi+1872], r8
	mov QWORD PTR [rdi+1880], r9
	mov QWORD PTR [rdi+1888], r10
	mov QWORD PTR [rdi+1896], r11
	mov QWORD PTR [rdi+1904], r12
	mov QWORD PTR [rdi+1912], r13
	mov QWORD PTR [rdi+1920], r14
	mov QWORD PTR [rdi+1928], r15
	movq rbx, xmm7
	movq rsi, xmm6
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1720
	call {vg_p521_win_sqr_adx}
	mov QWORD PTR [rdi+1936], rbp
	mov QWORD PTR [rdi+1944], r8
	mov QWORD PTR [rdi+1952], r9
	mov QWORD PTR [rdi+1960], r10
	mov QWORD PTR [rdi+1968], r11
	mov QWORD PTR [rdi+1976], r12
	mov QWORD PTR [rdi+1984], r13
	mov QWORD PTR [rdi+1992], r14
	mov QWORD PTR [rdi+2000], r15
	movq rbx, xmm7
	mov rbp, QWORD PTR [rdi+1864]
	mov r8, QWORD PTR [rdi+1872]
	mov r9, QWORD PTR [rdi+1880]
	mov r10, QWORD PTR [rdi+1888]
	mov r11, QWORD PTR [rdi+1896]
	mov r12, QWORD PTR [rdi+1904]
	mov r13, QWORD PTR [rdi+1912]
	mov r14, QWORD PTR [rdi+1920]
	mov r15, QWORD PTR [rdi+1928]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	add rbp, QWORD PTR [rdi+1936]
	adc r8, QWORD PTR [rdi+1944]
	adc r9, QWORD PTR [rdi+1952]
	adc r10, QWORD PTR [rdi+1960]
	adc r11, QWORD PTR [rdi+1968]
	adc r12, QWORD PTR [rdi+1976]
	adc r13, QWORD PTR [rdi+1984]
	adc r14, QWORD PTR [rdi+1992]
	adc r15, QWORD PTR [rdi+2000]
	add r15, 1024
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	mov QWORD PTR [rdi+1072], rbp
	mov QWORD PTR [rdi+1080], r8
	mov QWORD PTR [rdi+1088], r9
	mov QWORD PTR [rdi+1096], r10
	mov QWORD PTR [rdi+1104], r11
	mov QWORD PTR [rdi+1112], r12
	mov QWORD PTR [rdi+1120], r13
	mov QWORD PTR [rdi+1128], r14
	mov QWORD PTR [rdi+1136], r15
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1792
	call {vg_p521_win_sqr_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1792], rbp
	mov QWORD PTR [rdi+1800], r8
	mov QWORD PTR [rdi+1808], r9
	mov QWORD PTR [rdi+1816], r10
	mov QWORD PTR [rdi+1824], r11
	mov QWORD PTR [rdi+1832], r12
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	movq rbx, xmm7
	mov rbp, QWORD PTR [rdi+1072]
	mov r8, QWORD PTR [rdi+1080]
	mov r9, QWORD PTR [rdi+1088]
	mov r10, QWORD PTR [rdi+1096]
	mov r11, QWORD PTR [rdi+1104]
	mov r12, QWORD PTR [rdi+1112]
	mov r13, QWORD PTR [rdi+1120]
	mov r14, QWORD PTR [rdi+1128]
	mov r15, QWORD PTR [rdi+1136]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1864]
	adc r8, QWORD PTR [rdi+1872]
	adc r9, QWORD PTR [rdi+1880]
	adc r10, QWORD PTR [rdi+1888]
	adc r11, QWORD PTR [rdi+1896]
	adc r12, QWORD PTR [rdi+1904]
	adc r13, QWORD PTR [rdi+1912]
	adc r14, QWORD PTR [rdi+1920]
	adc r15, QWORD PTR [rdi+1928]
	add r15, 512
	mov QWORD PTR [rdi+1864], rbp
	mov QWORD PTR [rdi+1872], r8
	mov QWORD PTR [rdi+1880], r9
	mov QWORD PTR [rdi+1888], r10
	mov QWORD PTR [rdi+1896], r11
	mov QWORD PTR [rdi+1904], r12
	mov QWORD PTR [rdi+1912], r13
	mov QWORD PTR [rdi+1920], r14
	mov QWORD PTR [rdi+1928], r15
	mov rbp, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+1728]
	mov r9, QWORD PTR [rdi+1736]
	mov r10, QWORD PTR [rdi+1744]
	mov r11, QWORD PTR [rdi+1752]
	mov r12, QWORD PTR [rdi+1760]
	mov r13, QWORD PTR [rdi+1768]
	mov r14, QWORD PTR [rdi+1776]
	mov r15, QWORD PTR [rdi+1784]
	add rbp, QWORD PTR [rdi+1720]
	adc r8, QWORD PTR [rdi+1728]
	adc r9, QWORD PTR [rdi+1736]
	adc r10, QWORD PTR [rdi+1744]
	adc r11, QWORD PTR [rdi+1752]
	adc r12, QWORD PTR [rdi+1760]
	adc r13, QWORD PTR [rdi+1768]
	adc r14, QWORD PTR [rdi+1776]
	adc r15, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1720
	mov rbx, rdi
	add rbx, 1864
	call {vg_p521_win_mul_adx}
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq rbx, xmm7
	movq rsi, xmm6
	mov rbp, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+1800]
	mov r9, QWORD PTR [rdi+1808]
	mov r10, QWORD PTR [rdi+1816]
	mov r11, QWORD PTR [rdi+1824]
	mov r12, QWORD PTR [rdi+1832]
	mov r13, QWORD PTR [rdi+1840]
	mov r14, QWORD PTR [rdi+1848]
	mov r15, QWORD PTR [rdi+1856]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1720]
	adc r8, QWORD PTR [rdi+1728]
	adc r9, QWORD PTR [rdi+1736]
	adc r10, QWORD PTR [rdi+1744]
	adc r11, QWORD PTR [rdi+1752]
	adc r12, QWORD PTR [rdi+1760]
	adc r13, QWORD PTR [rdi+1768]
	adc r14, QWORD PTR [rdi+1776]
	adc r15, QWORD PTR [rdi+1784]
	add r15, 512
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	mov QWORD PTR [rdi+1144], rbp
	mov QWORD PTR [rdi+1152], r8
	mov QWORD PTR [rdi+1160], r9
	mov QWORD PTR [rdi+1168], r10
	mov QWORD PTR [rdi+1176], r11
	mov QWORD PTR [rdi+1184], r12
	mov QWORD PTR [rdi+1192], r13
	mov QWORD PTR [rdi+1200], r14
	mov QWORD PTR [rdi+1208], r15
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1216
	call {vg_p521_win_sqr_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq rbx, xmm7
	mov rbp, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+1728]
	mov r9, QWORD PTR [rdi+1736]
	mov r10, QWORD PTR [rdi+1744]
	mov r11, QWORD PTR [rdi+1752]
	mov r12, QWORD PTR [rdi+1760]
	mov r13, QWORD PTR [rdi+1768]
	mov r14, QWORD PTR [rdi+1776]
	mov r15, QWORD PTR [rdi+1784]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1072]
	adc r8, QWORD PTR [rdi+1080]
	adc r9, QWORD PTR [rdi+1088]
	adc r10, QWORD PTR [rdi+1096]
	adc r11, QWORD PTR [rdi+1104]
	adc r12, QWORD PTR [rdi+1112]
	adc r13, QWORD PTR [rdi+1120]
	adc r14, QWORD PTR [rdi+1128]
	adc r15, QWORD PTR [rdi+1136]
	add r15, 512
	mov QWORD PTR [rdi+1792], rbp
	mov QWORD PTR [rdi+1800], r8
	mov QWORD PTR [rdi+1808], r9
	mov QWORD PTR [rdi+1816], r10
	mov QWORD PTR [rdi+1824], r11
	mov QWORD PTR [rdi+1832], r12
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1144
	mov rbx, rdi
	add rbx, 1216
	call {vg_p521_win_mul_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1216], rbp
	mov QWORD PTR [rdi+1224], r8
	mov QWORD PTR [rdi+1232], r9
	mov QWORD PTR [rdi+1240], r10
	mov QWORD PTR [rdi+1248], r11
	mov QWORD PTR [rdi+1256], r12
	mov QWORD PTR [rdi+1264], r13
	mov QWORD PTR [rdi+1272], r14
	mov QWORD PTR [rdi+1280], r15
	movq rbx, xmm7
	movq rsi, xmm6
	mov rbp, QWORD PTR [rdi+1072]
	mov r8, QWORD PTR [rdi+1080]
	mov r9, QWORD PTR [rdi+1088]
	mov r10, QWORD PTR [rdi+1096]
	mov r11, QWORD PTR [rdi+1104]
	mov r12, QWORD PTR [rdi+1112]
	mov r13, QWORD PTR [rdi+1120]
	mov r14, QWORD PTR [rdi+1128]
	mov r15, QWORD PTR [rdi+1136]
	add rbp, QWORD PTR [rdi+1720]
	adc r8, QWORD PTR [rdi+1728]
	adc r9, QWORD PTR [rdi+1736]
	adc r10, QWORD PTR [rdi+1744]
	adc r11, QWORD PTR [rdi+1752]
	adc r12, QWORD PTR [rdi+1760]
	adc r13, QWORD PTR [rdi+1768]
	adc r14, QWORD PTR [rdi+1776]
	adc r15, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1792
	mov rbx, rdi
	add rbx, 1720
	call {vg_p521_win_mul_adx}
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq rbx, xmm7
	movq rsi, xmm6
	mov rbp, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+1728]
	mov r9, QWORD PTR [rdi+1736]
	mov r10, QWORD PTR [rdi+1744]
	mov r11, QWORD PTR [rdi+1752]
	mov r12, QWORD PTR [rdi+1760]
	mov r13, QWORD PTR [rdi+1768]
	mov r14, QWORD PTR [rdi+1776]
	mov r15, QWORD PTR [rdi+1784]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	add rbp, QWORD PTR [rdi+1720]
	adc r8, QWORD PTR [rdi+1728]
	adc r9, QWORD PTR [rdi+1736]
	adc r10, QWORD PTR [rdi+1744]
	adc r11, QWORD PTR [rdi+1752]
	adc r12, QWORD PTR [rdi+1760]
	adc r13, QWORD PTR [rdi+1768]
	adc r14, QWORD PTR [rdi+1776]
	adc r15, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1144
	call {vg_p521_win_sqr_adx}
	mov QWORD PTR [rdi+1792], rbp
	mov QWORD PTR [rdi+1800], r8
	mov QWORD PTR [rdi+1808], r9
	mov QWORD PTR [rdi+1816], r10
	mov QWORD PTR [rdi+1824], r11
	mov QWORD PTR [rdi+1832], r12
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	movq rbx, xmm7
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1072
	mov rbx, rdi
	add rbx, 1792
	call {vg_p521_win_mul_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1864], rbp
	mov QWORD PTR [rdi+1872], r8
	mov QWORD PTR [rdi+1880], r9
	mov QWORD PTR [rdi+1888], r10
	mov QWORD PTR [rdi+1896], r11
	mov QWORD PTR [rdi+1904], r12
	mov QWORD PTR [rdi+1912], r13
	mov QWORD PTR [rdi+1920], r14
	mov QWORD PTR [rdi+1928], r15
	movq rbx, xmm7
	movq rsi, xmm6
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1720
	call {vg_p521_win_sqr_adx}
	mov QWORD PTR [rdi+1936], rbp
	mov QWORD PTR [rdi+1944], r8
	mov QWORD PTR [rdi+1952], r9
	mov QWORD PTR [rdi+1960], r10
	mov QWORD PTR [rdi+1968], r11
	mov QWORD PTR [rdi+1976], r12
	mov QWORD PTR [rdi+1984], r13
	mov QWORD PTR [rdi+1992], r14
	mov QWORD PTR [rdi+2000], r15
	movq rbx, xmm7
	mov rbp, QWORD PTR [rdi+1864]
	mov r8, QWORD PTR [rdi+1872]
	mov r9, QWORD PTR [rdi+1880]
	mov r10, QWORD PTR [rdi+1888]
	mov r11, QWORD PTR [rdi+1896]
	mov r12, QWORD PTR [rdi+1904]
	mov r13, QWORD PTR [rdi+1912]
	mov r14, QWORD PTR [rdi+1920]
	mov r15, QWORD PTR [rdi+1928]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	add rbp, QWORD PTR [rdi+1936]
	adc r8, QWORD PTR [rdi+1944]
	adc r9, QWORD PTR [rdi+1952]
	adc r10, QWORD PTR [rdi+1960]
	adc r11, QWORD PTR [rdi+1968]
	adc r12, QWORD PTR [rdi+1976]
	adc r13, QWORD PTR [rdi+1984]
	adc r14, QWORD PTR [rdi+1992]
	adc r15, QWORD PTR [rdi+2000]
	add r15, 1024
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	mov QWORD PTR [rdi+1072], rbp
	mov QWORD PTR [rdi+1080], r8
	mov QWORD PTR [rdi+1088], r9
	mov QWORD PTR [rdi+1096], r10
	mov QWORD PTR [rdi+1104], r11
	mov QWORD PTR [rdi+1112], r12
	mov QWORD PTR [rdi+1120], r13
	mov QWORD PTR [rdi+1128], r14
	mov QWORD PTR [rdi+1136], r15
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1792
	call {vg_p521_win_sqr_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1792], rbp
	mov QWORD PTR [rdi+1800], r8
	mov QWORD PTR [rdi+1808], r9
	mov QWORD PTR [rdi+1816], r10
	mov QWORD PTR [rdi+1824], r11
	mov QWORD PTR [rdi+1832], r12
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	movq rbx, xmm7
	mov rbp, QWORD PTR [rdi+1072]
	mov r8, QWORD PTR [rdi+1080]
	mov r9, QWORD PTR [rdi+1088]
	mov r10, QWORD PTR [rdi+1096]
	mov r11, QWORD PTR [rdi+1104]
	mov r12, QWORD PTR [rdi+1112]
	mov r13, QWORD PTR [rdi+1120]
	mov r14, QWORD PTR [rdi+1128]
	mov r15, QWORD PTR [rdi+1136]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1864]
	adc r8, QWORD PTR [rdi+1872]
	adc r9, QWORD PTR [rdi+1880]
	adc r10, QWORD PTR [rdi+1888]
	adc r11, QWORD PTR [rdi+1896]
	adc r12, QWORD PTR [rdi+1904]
	adc r13, QWORD PTR [rdi+1912]
	adc r14, QWORD PTR [rdi+1920]
	adc r15, QWORD PTR [rdi+1928]
	add r15, 512
	mov QWORD PTR [rdi+1864], rbp
	mov QWORD PTR [rdi+1872], r8
	mov QWORD PTR [rdi+1880], r9
	mov QWORD PTR [rdi+1888], r10
	mov QWORD PTR [rdi+1896], r11
	mov QWORD PTR [rdi+1904], r12
	mov QWORD PTR [rdi+1912], r13
	mov QWORD PTR [rdi+1920], r14
	mov QWORD PTR [rdi+1928], r15
	mov rbp, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+1728]
	mov r9, QWORD PTR [rdi+1736]
	mov r10, QWORD PTR [rdi+1744]
	mov r11, QWORD PTR [rdi+1752]
	mov r12, QWORD PTR [rdi+1760]
	mov r13, QWORD PTR [rdi+1768]
	mov r14, QWORD PTR [rdi+1776]
	mov r15, QWORD PTR [rdi+1784]
	add rbp, QWORD PTR [rdi+1720]
	adc r8, QWORD PTR [rdi+1728]
	adc r9, QWORD PTR [rdi+1736]
	adc r10, QWORD PTR [rdi+1744]
	adc r11, QWORD PTR [rdi+1752]
	adc r12, QWORD PTR [rdi+1760]
	adc r13, QWORD PTR [rdi+1768]
	adc r14, QWORD PTR [rdi+1776]
	adc r15, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1720
	mov rbx, rdi
	add rbx, 1864
	call {vg_p521_win_mul_adx}
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq rbx, xmm7
	movq rsi, xmm6
	mov rbp, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+1800]
	mov r9, QWORD PTR [rdi+1808]
	mov r10, QWORD PTR [rdi+1816]
	mov r11, QWORD PTR [rdi+1824]
	mov r12, QWORD PTR [rdi+1832]
	mov r13, QWORD PTR [rdi+1840]
	mov r14, QWORD PTR [rdi+1848]
	mov r15, QWORD PTR [rdi+1856]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1720]
	adc r8, QWORD PTR [rdi+1728]
	adc r9, QWORD PTR [rdi+1736]
	adc r10, QWORD PTR [rdi+1744]
	adc r11, QWORD PTR [rdi+1752]
	adc r12, QWORD PTR [rdi+1760]
	adc r13, QWORD PTR [rdi+1768]
	adc r14, QWORD PTR [rdi+1776]
	adc r15, QWORD PTR [rdi+1784]
	add r15, 512
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	mov QWORD PTR [rdi+1144], rbp
	mov QWORD PTR [rdi+1152], r8
	mov QWORD PTR [rdi+1160], r9
	mov QWORD PTR [rdi+1168], r10
	mov QWORD PTR [rdi+1176], r11
	mov QWORD PTR [rdi+1184], r12
	mov QWORD PTR [rdi+1192], r13
	mov QWORD PTR [rdi+1200], r14
	mov QWORD PTR [rdi+1208], r15
	sub rbx, 4096
	cmp rbx, 4096
	jae 218b
	mov rbp, QWORD PTR [rdi+1144]
	mov r8, QWORD PTR [rdi+1152]
	mov r9, QWORD PTR [rdi+1160]
	mov r10, QWORD PTR [rdi+1168]
	mov r11, QWORD PTR [rdi+1176]
	mov r12, QWORD PTR [rdi+1184]
	mov r13, QWORD PTR [rdi+1192]
	mov r14, QWORD PTR [rdi+1200]
	mov r15, QWORD PTR [rdi+1208]
	mov rax, rbp
	and rax, 1
	shl rax, 8
	mov rcx, r15
	shr rcx, 1
	add rcx, rax
	shld r15, r14, 63
	shld r14, r13, 63
	shld r13, r12, 63
	shld r12, r11, 63
	shld r11, r10, 63
	shld r10, r9, 63
	shld r9, r8, 63
	shld r8, rbp, 63
	mov QWORD PTR [rdi+1144], r8
	mov QWORD PTR [rdi+1152], r9
	mov QWORD PTR [rdi+1160], r10
	mov QWORD PTR [rdi+1168], r11
	mov QWORD PTR [rdi+1176], r12
	mov QWORD PTR [rdi+1184], r13
	mov QWORD PTR [rdi+1192], r14
	mov QWORD PTR [rdi+1200], r15
	mov QWORD PTR [rdi+1208], rcx
	add rdi, 1144
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -864
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 864
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1144
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -792
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 792
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1072
	add rdi, 1216
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -936
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 936
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1216
	mov rax, rbx
	mov ecx, 4
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+5323]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+5322]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+5321]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+5320]
	add rax, rdx
	sub rax, 8
	mov rdx, rax
	shr rdx, 63
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	mov r8, rax
	mov rdx, rdi
	add rdx, 6112
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	mov ecx, 1
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+16]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+32]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+48]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+64]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+80]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+96]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+112]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+128]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+144]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+160]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+176]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+192]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+200]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 2
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+216]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+232]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+248]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+264]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+280]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+296]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+312]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+328]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+344]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+360]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+376]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+392]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+408]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+416]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 3
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+432]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+448]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+464]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+480]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+496]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+512]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+528]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+544]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+560]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+576]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+592]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+608]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+624]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+632]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 4
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+648]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+664]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+680]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+696]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+712]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+728]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+744]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+760]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+776]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+792]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+808]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+824]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+840]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+848]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 5
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+864]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+880]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+896]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+912]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+928]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+944]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+960]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+976]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+992]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1008]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1024]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1040]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1056]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1064]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 6
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1080]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1096]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1112]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1128]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1144]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1160]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1176]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1192]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1208]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1224]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1240]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1256]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1272]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1280]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 7
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1296]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1312]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1328]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1344]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1360]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1376]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1392]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1408]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1424]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1440]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1456]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1472]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1488]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1496]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 8
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1512]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1528]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1544]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1560]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1576]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1592]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1608]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1624]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1640]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1656]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1672]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1688]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1704]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1712]
	pand xmm14, xmm15
	por xmm13, xmm14
	movdqu XMMWORD PTR [rdi+1504], xmm0
	movdqu XMMWORD PTR [rdi+1520], xmm1
	movdqu XMMWORD PTR [rdi+1536], xmm2
	movdqu XMMWORD PTR [rdi+1552], xmm3
	movdqu XMMWORD PTR [rdi+1568], xmm4
	movdqu XMMWORD PTR [rdi+1584], xmm5
	movdqu XMMWORD PTR [rdi+1600], xmm6
	movdqu XMMWORD PTR [rdi+1616], xmm7
	movdqu XMMWORD PTR [rdi+1632], xmm8
	movdqu XMMWORD PTR [rdi+1648], xmm9
	movdqu XMMWORD PTR [rdi+1664], xmm10
	movdqu XMMWORD PTR [rdi+1680], xmm11
	movdqu XMMWORD PTR [rdi+1696], xmm12
	movdqu XMMWORD PTR [rdi+1704], xmm13
	mov rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movabs rax, 36028797018963968
	and rax, rcx
	or rax, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+1576], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+1584], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+1592], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+1600], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+1608], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+1616], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1624]
	mov QWORD PTR [rdi+1624], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1632]
	mov QWORD PTR [rdi+1632], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1640]
	mov QWORD PTR [rdi+1640], rax
	add rdi, 280
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 1296
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2224
	mov rax, rbx
	mov ecx, 4
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+5323]
	sub rax, 1
	mov rcx, rax
	mov rax, QWORD PTR [rdi+1576]
	mov rdx, QWORD PTR [rdi+2224]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rdi+1584]
	mov rdx, QWORD PTR [rdi+2232]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rdi+1592]
	mov rdx, QWORD PTR [rdi+2240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rdi+1600]
	mov rdx, QWORD PTR [rdi+2248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1600], rax
	mov rax, QWORD PTR [rdi+1608]
	mov rdx, QWORD PTR [rdi+2256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1608], rax
	mov rax, QWORD PTR [rdi+1616]
	mov rdx, QWORD PTR [rdi+2264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1616], rax
	mov rax, QWORD PTR [rdi+1624]
	mov rdx, QWORD PTR [rdi+2272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1624], rax
	mov rax, QWORD PTR [rdi+1632]
	mov rdx, QWORD PTR [rdi+2280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1632], rax
	mov rax, QWORD PTR [rdi+1640]
	mov rdx, QWORD PTR [rdi+2288]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1640], rax
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1216
	call {vg_p521_win_sqr_adx}
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq rbx, xmm7
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1504
	mov rbx, rdi
	add rbx, 1720
	call {vg_p521_win_mul_adx}
	mov QWORD PTR [rdi+1792], rbp
	mov QWORD PTR [rdi+1800], r8
	mov QWORD PTR [rdi+1808], r9
	mov QWORD PTR [rdi+1816], r10
	mov QWORD PTR [rdi+1824], r11
	mov QWORD PTR [rdi+1832], r12
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	movq rbx, xmm7
	movq rsi, xmm6
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1216
	mov rbx, rdi
	add rbx, 1720
	call {vg_p521_win_mul_adx}
	mov QWORD PTR [rdi+1864], rbp
	mov QWORD PTR [rdi+1872], r8
	mov QWORD PTR [rdi+1880], r9
	mov QWORD PTR [rdi+1888], r10
	mov QWORD PTR [rdi+1896], r11
	mov QWORD PTR [rdi+1904], r12
	mov QWORD PTR [rdi+1912], r13
	mov QWORD PTR [rdi+1920], r14
	mov QWORD PTR [rdi+1928], r15
	movq rbx, xmm7
	movq rsi, xmm6
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1576
	mov rbx, rdi
	add rbx, 1864
	call {vg_p521_win_mul_adx}
	mov QWORD PTR [rdi+1864], rbp
	mov QWORD PTR [rdi+1872], r8
	mov QWORD PTR [rdi+1880], r9
	mov QWORD PTR [rdi+1888], r10
	mov QWORD PTR [rdi+1896], r11
	mov QWORD PTR [rdi+1904], r12
	mov QWORD PTR [rdi+1912], r13
	mov QWORD PTR [rdi+1920], r14
	mov QWORD PTR [rdi+1928], r15
	movq rbx, xmm7
	movq rsi, xmm6
	mov rbp, QWORD PTR [rdi+1072]
	mov r8, QWORD PTR [rdi+1080]
	mov r9, QWORD PTR [rdi+1088]
	mov r10, QWORD PTR [rdi+1096]
	mov r11, QWORD PTR [rdi+1104]
	mov r12, QWORD PTR [rdi+1112]
	mov r13, QWORD PTR [rdi+1120]
	mov r14, QWORD PTR [rdi+1128]
	mov r15, QWORD PTR [rdi+1136]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1792]
	adc r8, QWORD PTR [rdi+1800]
	adc r9, QWORD PTR [rdi+1808]
	adc r10, QWORD PTR [rdi+1816]
	adc r11, QWORD PTR [rdi+1824]
	adc r12, QWORD PTR [rdi+1832]
	adc r13, QWORD PTR [rdi+1840]
	adc r14, QWORD PTR [rdi+1848]
	adc r15, QWORD PTR [rdi+1856]
	add r15, 512
	mov QWORD PTR [rdi+1792], rbp
	mov QWORD PTR [rdi+1800], r8
	mov QWORD PTR [rdi+1808], r9
	mov QWORD PTR [rdi+1816], r10
	mov QWORD PTR [rdi+1824], r11
	mov QWORD PTR [rdi+1832], r12
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	mov rbp, QWORD PTR [rdi+1144]
	mov r8, QWORD PTR [rdi+1152]
	mov r9, QWORD PTR [rdi+1160]
	mov r10, QWORD PTR [rdi+1168]
	mov r11, QWORD PTR [rdi+1176]
	mov r12, QWORD PTR [rdi+1184]
	mov r13, QWORD PTR [rdi+1192]
	mov r14, QWORD PTR [rdi+1200]
	mov r15, QWORD PTR [rdi+1208]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1864]
	adc r8, QWORD PTR [rdi+1872]
	adc r9, QWORD PTR [rdi+1880]
	adc r10, QWORD PTR [rdi+1888]
	adc r11, QWORD PTR [rdi+1896]
	adc r12, QWORD PTR [rdi+1904]
	adc r13, QWORD PTR [rdi+1912]
	adc r14, QWORD PTR [rdi+1920]
	adc r15, QWORD PTR [rdi+1928]
	add r15, 512
	mov QWORD PTR [rdi+1864], rbp
	mov QWORD PTR [rdi+1872], r8
	mov QWORD PTR [rdi+1880], r9
	mov QWORD PTR [rdi+1888], r10
	mov QWORD PTR [rdi+1896], r11
	mov QWORD PTR [rdi+1904], r12
	mov QWORD PTR [rdi+1912], r13
	mov QWORD PTR [rdi+1920], r14
	mov QWORD PTR [rdi+1928], r15
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1792
	call {vg_p521_win_sqr_adx}
	mov QWORD PTR [rdi+1936], rbp
	mov QWORD PTR [rdi+1944], r8
	mov QWORD PTR [rdi+1952], r9
	mov QWORD PTR [rdi+1960], r10
	mov QWORD PTR [rdi+1968], r11
	mov QWORD PTR [rdi+1976], r12
	mov QWORD PTR [rdi+1984], r13
	mov QWORD PTR [rdi+1992], r14
	mov QWORD PTR [rdi+2000], r15
	movq rbx, xmm7
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1792
	mov rbx, rdi
	add rbx, 1936
	call {vg_p521_win_mul_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+2008], rbp
	mov QWORD PTR [rdi+2016], r8
	mov QWORD PTR [rdi+2024], r9
	mov QWORD PTR [rdi+2032], r10
	mov QWORD PTR [rdi+2040], r11
	mov QWORD PTR [rdi+2048], r12
	mov QWORD PTR [rdi+2056], r13
	mov QWORD PTR [rdi+2064], r14
	mov QWORD PTR [rdi+2072], r15
	movq rbx, xmm7
	movq rsi, xmm6
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1072
	mov rbx, rdi
	add rbx, 1936
	call {vg_p521_win_mul_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1936], rbp
	mov QWORD PTR [rdi+1944], r8
	mov QWORD PTR [rdi+1952], r9
	mov QWORD PTR [rdi+1960], r10
	mov QWORD PTR [rdi+1968], r11
	mov QWORD PTR [rdi+1976], r12
	mov QWORD PTR [rdi+1984], r13
	mov QWORD PTR [rdi+1992], r14
	mov QWORD PTR [rdi+2000], r15
	movq rbx, xmm7
	movq rsi, xmm6
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1864
	call {vg_p521_win_sqr_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1288], rbp
	mov QWORD PTR [rdi+1296], r8
	mov QWORD PTR [rdi+1304], r9
	mov QWORD PTR [rdi+1312], r10
	mov QWORD PTR [rdi+1320], r11
	mov QWORD PTR [rdi+1328], r12
	mov QWORD PTR [rdi+1336], r13
	mov QWORD PTR [rdi+1344], r14
	mov QWORD PTR [rdi+1352], r15
	movq rbx, xmm7
	mov rbp, QWORD PTR [rdi+2008]
	mov r8, QWORD PTR [rdi+2016]
	mov r9, QWORD PTR [rdi+2024]
	mov r10, QWORD PTR [rdi+2032]
	mov r11, QWORD PTR [rdi+2040]
	mov r12, QWORD PTR [rdi+2048]
	mov r13, QWORD PTR [rdi+2056]
	mov r14, QWORD PTR [rdi+2064]
	mov r15, QWORD PTR [rdi+2072]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1288]
	adc r8, QWORD PTR [rdi+1296]
	adc r9, QWORD PTR [rdi+1304]
	adc r10, QWORD PTR [rdi+1312]
	adc r11, QWORD PTR [rdi+1320]
	adc r12, QWORD PTR [rdi+1328]
	adc r13, QWORD PTR [rdi+1336]
	adc r14, QWORD PTR [rdi+1344]
	adc r15, QWORD PTR [rdi+1352]
	add r15, 512
	mov QWORD PTR [rdi+1288], rbp
	mov QWORD PTR [rdi+1296], r8
	mov QWORD PTR [rdi+1304], r9
	mov QWORD PTR [rdi+1312], r10
	mov QWORD PTR [rdi+1320], r11
	mov QWORD PTR [rdi+1328], r12
	mov QWORD PTR [rdi+1336], r13
	mov QWORD PTR [rdi+1344], r14
	mov QWORD PTR [rdi+1352], r15
	mov rbp, QWORD PTR [rdi+1936]
	mov r8, QWORD PTR [rdi+1944]
	mov r9, QWORD PTR [rdi+1952]
	mov r10, QWORD PTR [rdi+1960]
	mov r11, QWORD PTR [rdi+1968]
	mov r12, QWORD PTR [rdi+1976]
	mov r13, QWORD PTR [rdi+1984]
	mov r14, QWORD PTR [rdi+1992]
	mov r15, QWORD PTR [rdi+2000]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	add rbp, QWORD PTR [rdi+1288]
	adc r8, QWORD PTR [rdi+1296]
	adc r9, QWORD PTR [rdi+1304]
	adc r10, QWORD PTR [rdi+1312]
	adc r11, QWORD PTR [rdi+1320]
	adc r12, QWORD PTR [rdi+1328]
	adc r13, QWORD PTR [rdi+1336]
	adc r14, QWORD PTR [rdi+1344]
	adc r15, QWORD PTR [rdi+1352]
	add r15, 1024
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	mov QWORD PTR [rdi+1288], rbp
	mov QWORD PTR [rdi+1296], r8
	mov QWORD PTR [rdi+1304], r9
	mov QWORD PTR [rdi+1312], r10
	mov QWORD PTR [rdi+1320], r11
	mov QWORD PTR [rdi+1328], r12
	mov QWORD PTR [rdi+1336], r13
	mov QWORD PTR [rdi+1344], r14
	mov QWORD PTR [rdi+1352], r15
	mov rbp, QWORD PTR [rdi+1288]
	mov r8, QWORD PTR [rdi+1296]
	mov r9, QWORD PTR [rdi+1304]
	mov r10, QWORD PTR [rdi+1312]
	mov r11, QWORD PTR [rdi+1320]
	mov r12, QWORD PTR [rdi+1328]
	mov r13, QWORD PTR [rdi+1336]
	mov r14, QWORD PTR [rdi+1344]
	mov r15, QWORD PTR [rdi+1352]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1936]
	adc r8, QWORD PTR [rdi+1944]
	adc r9, QWORD PTR [rdi+1952]
	adc r10, QWORD PTR [rdi+1960]
	adc r11, QWORD PTR [rdi+1968]
	adc r12, QWORD PTR [rdi+1976]
	adc r13, QWORD PTR [rdi+1984]
	adc r14, QWORD PTR [rdi+1992]
	adc r15, QWORD PTR [rdi+2000]
	add r15, 512
	mov QWORD PTR [rdi+1936], rbp
	mov QWORD PTR [rdi+1944], r8
	mov QWORD PTR [rdi+1952], r9
	mov QWORD PTR [rdi+1960], r10
	mov QWORD PTR [rdi+1968], r11
	mov QWORD PTR [rdi+1976], r12
	mov QWORD PTR [rdi+1984], r13
	mov QWORD PTR [rdi+1992], r14
	mov QWORD PTR [rdi+2000], r15
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1864
	mov rbx, rdi
	add rbx, 1936
	call {vg_p521_win_mul_adx}
	mov QWORD PTR [rdi+1936], rbp
	mov QWORD PTR [rdi+1944], r8
	mov QWORD PTR [rdi+1952], r9
	mov QWORD PTR [rdi+1960], r10
	mov QWORD PTR [rdi+1968], r11
	mov QWORD PTR [rdi+1976], r12
	mov QWORD PTR [rdi+1984], r13
	mov QWORD PTR [rdi+1992], r14
	mov QWORD PTR [rdi+2000], r15
	movq rbx, xmm7
	movq rsi, xmm6
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1144
	mov rbx, rdi
	add rbx, 2008
	call {vg_p521_win_mul_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+2008], rbp
	mov QWORD PTR [rdi+2016], r8
	mov QWORD PTR [rdi+2024], r9
	mov QWORD PTR [rdi+2032], r10
	mov QWORD PTR [rdi+2040], r11
	mov QWORD PTR [rdi+2048], r12
	mov QWORD PTR [rdi+2056], r13
	mov QWORD PTR [rdi+2064], r14
	mov QWORD PTR [rdi+2072], r15
	movq rbx, xmm7
	movq rsi, xmm6
	mov rbp, QWORD PTR [rdi+2008]
	mov r8, QWORD PTR [rdi+2016]
	mov r9, QWORD PTR [rdi+2024]
	mov r10, QWORD PTR [rdi+2032]
	mov r11, QWORD PTR [rdi+2040]
	mov r12, QWORD PTR [rdi+2048]
	mov r13, QWORD PTR [rdi+2056]
	mov r14, QWORD PTR [rdi+2064]
	mov r15, QWORD PTR [rdi+2072]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1936]
	adc r8, QWORD PTR [rdi+1944]
	adc r9, QWORD PTR [rdi+1952]
	adc r10, QWORD PTR [rdi+1960]
	adc r11, QWORD PTR [rdi+1968]
	adc r12, QWORD PTR [rdi+1976]
	adc r13, QWORD PTR [rdi+1984]
	adc r14, QWORD PTR [rdi+1992]
	adc r15, QWORD PTR [rdi+2000]
	add r15, 512
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	mov QWORD PTR [rdi+1360], rbp
	mov QWORD PTR [rdi+1368], r8
	mov QWORD PTR [rdi+1376], r9
	mov QWORD PTR [rdi+1384], r10
	mov QWORD PTR [rdi+1392], r11
	mov QWORD PTR [rdi+1400], r12
	mov QWORD PTR [rdi+1408], r13
	mov QWORD PTR [rdi+1416], r14
	mov QWORD PTR [rdi+1424], r15
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1216
	mov rbx, rdi
	add rbx, 1792
	call {vg_p521_win_mul_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1432], rbp
	mov QWORD PTR [rdi+1440], r8
	mov QWORD PTR [rdi+1448], r9
	mov QWORD PTR [rdi+1456], r10
	mov QWORD PTR [rdi+1464], r11
	mov QWORD PTR [rdi+1472], r12
	mov QWORD PTR [rdi+1480], r13
	mov QWORD PTR [rdi+1488], r14
	mov QWORD PTR [rdi+1496], r15
	movq rbx, xmm7
	movq rsi, xmm6
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -1008
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 1008
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -1080
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 1080
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -1152
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 1152
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov rdx, QWORD PTR [rdi+1648]
	or rdx, QWORD PTR [rdi+1656]
	or rdx, QWORD PTR [rdi+1664]
	or rdx, QWORD PTR [rdi+1672]
	or rdx, QWORD PTR [rdi+1680]
	or rdx, QWORD PTR [rdi+1688]
	or rdx, QWORD PTR [rdi+1696]
	or rdx, QWORD PTR [rdi+1704]
	or rdx, QWORD PTR [rdi+1712]
	cmp rdx, 1
	sbb rdx, rdx
	mov rcx, rdx
	mov rax, QWORD PTR [rdi+1288]
	mov rdx, QWORD PTR [rdi+1072]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1288], rax
	mov rax, QWORD PTR [rdi+1296]
	mov rdx, QWORD PTR [rdi+1080]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1296], rax
	mov rax, QWORD PTR [rdi+1304]
	mov rdx, QWORD PTR [rdi+1088]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1304], rax
	mov rax, QWORD PTR [rdi+1312]
	mov rdx, QWORD PTR [rdi+1096]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1312], rax
	mov rax, QWORD PTR [rdi+1320]
	mov rdx, QWORD PTR [rdi+1104]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1320], rax
	mov rax, QWORD PTR [rdi+1328]
	mov rdx, QWORD PTR [rdi+1112]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1328], rax
	mov rax, QWORD PTR [rdi+1336]
	mov rdx, QWORD PTR [rdi+1120]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1336], rax
	mov rax, QWORD PTR [rdi+1344]
	mov rdx, QWORD PTR [rdi+1128]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1344], rax
	mov rax, QWORD PTR [rdi+1352]
	mov rdx, QWORD PTR [rdi+1136]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1352], rax
	mov rax, QWORD PTR [rdi+1360]
	mov rdx, QWORD PTR [rdi+1144]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+1368]
	mov rdx, QWORD PTR [rdi+1152]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+1376]
	mov rdx, QWORD PTR [rdi+1160]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+1384]
	mov rdx, QWORD PTR [rdi+1168]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+1392]
	mov rdx, QWORD PTR [rdi+1176]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+1400]
	mov rdx, QWORD PTR [rdi+1184]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+1408]
	mov rdx, QWORD PTR [rdi+1192]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+1416]
	mov rdx, QWORD PTR [rdi+1200]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+1424]
	mov rdx, QWORD PTR [rdi+1208]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1424], rax
	mov rax, QWORD PTR [rdi+1432]
	mov rdx, QWORD PTR [rdi+1216]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1432], rax
	mov rax, QWORD PTR [rdi+1440]
	mov rdx, QWORD PTR [rdi+1224]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1440], rax
	mov rax, QWORD PTR [rdi+1448]
	mov rdx, QWORD PTR [rdi+1232]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1448], rax
	mov rax, QWORD PTR [rdi+1456]
	mov rdx, QWORD PTR [rdi+1240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+1464]
	mov rdx, QWORD PTR [rdi+1248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+1472]
	mov rdx, QWORD PTR [rdi+1256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+1480]
	mov rdx, QWORD PTR [rdi+1264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+1488]
	mov rdx, QWORD PTR [rdi+1272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+1496]
	mov rdx, QWORD PTR [rdi+1280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1496], rax
	mov rdx, QWORD PTR [rdi+1216]
	or rdx, QWORD PTR [rdi+1224]
	or rdx, QWORD PTR [rdi+1232]
	or rdx, QWORD PTR [rdi+1240]
	or rdx, QWORD PTR [rdi+1248]
	or rdx, QWORD PTR [rdi+1256]
	or rdx, QWORD PTR [rdi+1264]
	or rdx, QWORD PTR [rdi+1272]
	or rdx, QWORD PTR [rdi+1280]
	cmp rdx, 1
	sbb rdx, rdx
	mov rcx, rdx
	mov rax, QWORD PTR [rdi+1288]
	mov rdx, QWORD PTR [rdi+1504]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov rdx, QWORD PTR [rdi+1512]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov rdx, QWORD PTR [rdi+1520]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov rdx, QWORD PTR [rdi+1528]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov rdx, QWORD PTR [rdi+1536]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov rdx, QWORD PTR [rdi+1544]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov rdx, QWORD PTR [rdi+1552]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov rdx, QWORD PTR [rdi+1560]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov rdx, QWORD PTR [rdi+1568]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov rdx, QWORD PTR [rdi+1576]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov rdx, QWORD PTR [rdi+1584]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov rdx, QWORD PTR [rdi+1592]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov rdx, QWORD PTR [rdi+1600]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov rdx, QWORD PTR [rdi+1608]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov rdx, QWORD PTR [rdi+1616]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov rdx, QWORD PTR [rdi+1624]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov rdx, QWORD PTR [rdi+1632]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov rdx, QWORD PTR [rdi+1640]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov rdx, QWORD PTR [rdi+1648]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov rdx, QWORD PTR [rdi+1656]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov rdx, QWORD PTR [rdi+1664]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov rdx, QWORD PTR [rdi+1672]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov rdx, QWORD PTR [rdi+1680]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov rdx, QWORD PTR [rdi+1688]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov rdx, QWORD PTR [rdi+1696]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov rdx, QWORD PTR [rdi+1704]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov rdx, QWORD PTR [rdi+1712]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1280], rax
	cmp rbx, 1
	jne 217b
	sub rbx, 1
	mov rbp, QWORD PTR [rdi+1144]
	mov r8, QWORD PTR [rdi+1152]
	mov r9, QWORD PTR [rdi+1160]
	mov r10, QWORD PTR [rdi+1168]
	mov r11, QWORD PTR [rdi+1176]
	mov r12, QWORD PTR [rdi+1184]
	mov r13, QWORD PTR [rdi+1192]
	mov r14, QWORD PTR [rdi+1200]
	mov r15, QWORD PTR [rdi+1208]
	add rbp, QWORD PTR [rdi+1144]
	adc r8, QWORD PTR [rdi+1152]
	adc r9, QWORD PTR [rdi+1160]
	adc r10, QWORD PTR [rdi+1168]
	adc r11, QWORD PTR [rdi+1176]
	adc r12, QWORD PTR [rdi+1184]
	adc r13, QWORD PTR [rdi+1192]
	adc r14, QWORD PTR [rdi+1200]
	adc r15, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+1144], rbp
	mov QWORD PTR [rdi+1152], r8
	mov QWORD PTR [rdi+1160], r9
	mov QWORD PTR [rdi+1168], r10
	mov QWORD PTR [rdi+1176], r11
	mov QWORD PTR [rdi+1184], r12
	mov QWORD PTR [rdi+1192], r13
	mov QWORD PTR [rdi+1200], r14
	mov QWORD PTR [rdi+1208], r15
	add rbx, 8192
219:
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1216
	call {vg_p521_win_sqr_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq rbx, xmm7
	mov rbp, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+1728]
	mov r9, QWORD PTR [rdi+1736]
	mov r10, QWORD PTR [rdi+1744]
	mov r11, QWORD PTR [rdi+1752]
	mov r12, QWORD PTR [rdi+1760]
	mov r13, QWORD PTR [rdi+1768]
	mov r14, QWORD PTR [rdi+1776]
	mov r15, QWORD PTR [rdi+1784]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1072]
	adc r8, QWORD PTR [rdi+1080]
	adc r9, QWORD PTR [rdi+1088]
	adc r10, QWORD PTR [rdi+1096]
	adc r11, QWORD PTR [rdi+1104]
	adc r12, QWORD PTR [rdi+1112]
	adc r13, QWORD PTR [rdi+1120]
	adc r14, QWORD PTR [rdi+1128]
	adc r15, QWORD PTR [rdi+1136]
	add r15, 512
	mov QWORD PTR [rdi+1792], rbp
	mov QWORD PTR [rdi+1800], r8
	mov QWORD PTR [rdi+1808], r9
	mov QWORD PTR [rdi+1816], r10
	mov QWORD PTR [rdi+1824], r11
	mov QWORD PTR [rdi+1832], r12
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1144
	mov rbx, rdi
	add rbx, 1216
	call {vg_p521_win_mul_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1216], rbp
	mov QWORD PTR [rdi+1224], r8
	mov QWORD PTR [rdi+1232], r9
	mov QWORD PTR [rdi+1240], r10
	mov QWORD PTR [rdi+1248], r11
	mov QWORD PTR [rdi+1256], r12
	mov QWORD PTR [rdi+1264], r13
	mov QWORD PTR [rdi+1272], r14
	mov QWORD PTR [rdi+1280], r15
	movq rbx, xmm7
	movq rsi, xmm6
	mov rbp, QWORD PTR [rdi+1072]
	mov r8, QWORD PTR [rdi+1080]
	mov r9, QWORD PTR [rdi+1088]
	mov r10, QWORD PTR [rdi+1096]
	mov r11, QWORD PTR [rdi+1104]
	mov r12, QWORD PTR [rdi+1112]
	mov r13, QWORD PTR [rdi+1120]
	mov r14, QWORD PTR [rdi+1128]
	mov r15, QWORD PTR [rdi+1136]
	add rbp, QWORD PTR [rdi+1720]
	adc r8, QWORD PTR [rdi+1728]
	adc r9, QWORD PTR [rdi+1736]
	adc r10, QWORD PTR [rdi+1744]
	adc r11, QWORD PTR [rdi+1752]
	adc r12, QWORD PTR [rdi+1760]
	adc r13, QWORD PTR [rdi+1768]
	adc r14, QWORD PTR [rdi+1776]
	adc r15, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1792
	mov rbx, rdi
	add rbx, 1720
	call {vg_p521_win_mul_adx}
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq rbx, xmm7
	movq rsi, xmm6
	mov rbp, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+1728]
	mov r9, QWORD PTR [rdi+1736]
	mov r10, QWORD PTR [rdi+1744]
	mov r11, QWORD PTR [rdi+1752]
	mov r12, QWORD PTR [rdi+1760]
	mov r13, QWORD PTR [rdi+1768]
	mov r14, QWORD PTR [rdi+1776]
	mov r15, QWORD PTR [rdi+1784]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	add rbp, QWORD PTR [rdi+1720]
	adc r8, QWORD PTR [rdi+1728]
	adc r9, QWORD PTR [rdi+1736]
	adc r10, QWORD PTR [rdi+1744]
	adc r11, QWORD PTR [rdi+1752]
	adc r12, QWORD PTR [rdi+1760]
	adc r13, QWORD PTR [rdi+1768]
	adc r14, QWORD PTR [rdi+1776]
	adc r15, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1144
	call {vg_p521_win_sqr_adx}
	mov QWORD PTR [rdi+1792], rbp
	mov QWORD PTR [rdi+1800], r8
	mov QWORD PTR [rdi+1808], r9
	mov QWORD PTR [rdi+1816], r10
	mov QWORD PTR [rdi+1824], r11
	mov QWORD PTR [rdi+1832], r12
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	movq rbx, xmm7
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1072
	mov rbx, rdi
	add rbx, 1792
	call {vg_p521_win_mul_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1864], rbp
	mov QWORD PTR [rdi+1872], r8
	mov QWORD PTR [rdi+1880], r9
	mov QWORD PTR [rdi+1888], r10
	mov QWORD PTR [rdi+1896], r11
	mov QWORD PTR [rdi+1904], r12
	mov QWORD PTR [rdi+1912], r13
	mov QWORD PTR [rdi+1920], r14
	mov QWORD PTR [rdi+1928], r15
	movq rbx, xmm7
	movq rsi, xmm6
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1720
	call {vg_p521_win_sqr_adx}
	mov QWORD PTR [rdi+1936], rbp
	mov QWORD PTR [rdi+1944], r8
	mov QWORD PTR [rdi+1952], r9
	mov QWORD PTR [rdi+1960], r10
	mov QWORD PTR [rdi+1968], r11
	mov QWORD PTR [rdi+1976], r12
	mov QWORD PTR [rdi+1984], r13
	mov QWORD PTR [rdi+1992], r14
	mov QWORD PTR [rdi+2000], r15
	movq rbx, xmm7
	mov rbp, QWORD PTR [rdi+1864]
	mov r8, QWORD PTR [rdi+1872]
	mov r9, QWORD PTR [rdi+1880]
	mov r10, QWORD PTR [rdi+1888]
	mov r11, QWORD PTR [rdi+1896]
	mov r12, QWORD PTR [rdi+1904]
	mov r13, QWORD PTR [rdi+1912]
	mov r14, QWORD PTR [rdi+1920]
	mov r15, QWORD PTR [rdi+1928]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	add rbp, QWORD PTR [rdi+1936]
	adc r8, QWORD PTR [rdi+1944]
	adc r9, QWORD PTR [rdi+1952]
	adc r10, QWORD PTR [rdi+1960]
	adc r11, QWORD PTR [rdi+1968]
	adc r12, QWORD PTR [rdi+1976]
	adc r13, QWORD PTR [rdi+1984]
	adc r14, QWORD PTR [rdi+1992]
	adc r15, QWORD PTR [rdi+2000]
	add r15, 1024
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	mov QWORD PTR [rdi+1072], rbp
	mov QWORD PTR [rdi+1080], r8
	mov QWORD PTR [rdi+1088], r9
	mov QWORD PTR [rdi+1096], r10
	mov QWORD PTR [rdi+1104], r11
	mov QWORD PTR [rdi+1112], r12
	mov QWORD PTR [rdi+1120], r13
	mov QWORD PTR [rdi+1128], r14
	mov QWORD PTR [rdi+1136], r15
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1792
	call {vg_p521_win_sqr_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1792], rbp
	mov QWORD PTR [rdi+1800], r8
	mov QWORD PTR [rdi+1808], r9
	mov QWORD PTR [rdi+1816], r10
	mov QWORD PTR [rdi+1824], r11
	mov QWORD PTR [rdi+1832], r12
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	movq rbx, xmm7
	mov rbp, QWORD PTR [rdi+1072]
	mov r8, QWORD PTR [rdi+1080]
	mov r9, QWORD PTR [rdi+1088]
	mov r10, QWORD PTR [rdi+1096]
	mov r11, QWORD PTR [rdi+1104]
	mov r12, QWORD PTR [rdi+1112]
	mov r13, QWORD PTR [rdi+1120]
	mov r14, QWORD PTR [rdi+1128]
	mov r15, QWORD PTR [rdi+1136]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1864]
	adc r8, QWORD PTR [rdi+1872]
	adc r9, QWORD PTR [rdi+1880]
	adc r10, QWORD PTR [rdi+1888]
	adc r11, QWORD PTR [rdi+1896]
	adc r12, QWORD PTR [rdi+1904]
	adc r13, QWORD PTR [rdi+1912]
	adc r14, QWORD PTR [rdi+1920]
	adc r15, QWORD PTR [rdi+1928]
	add r15, 512
	mov QWORD PTR [rdi+1864], rbp
	mov QWORD PTR [rdi+1872], r8
	mov QWORD PTR [rdi+1880], r9
	mov QWORD PTR [rdi+1888], r10
	mov QWORD PTR [rdi+1896], r11
	mov QWORD PTR [rdi+1904], r12
	mov QWORD PTR [rdi+1912], r13
	mov QWORD PTR [rdi+1920], r14
	mov QWORD PTR [rdi+1928], r15
	mov rbp, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+1728]
	mov r9, QWORD PTR [rdi+1736]
	mov r10, QWORD PTR [rdi+1744]
	mov r11, QWORD PTR [rdi+1752]
	mov r12, QWORD PTR [rdi+1760]
	mov r13, QWORD PTR [rdi+1768]
	mov r14, QWORD PTR [rdi+1776]
	mov r15, QWORD PTR [rdi+1784]
	add rbp, QWORD PTR [rdi+1720]
	adc r8, QWORD PTR [rdi+1728]
	adc r9, QWORD PTR [rdi+1736]
	adc r10, QWORD PTR [rdi+1744]
	adc r11, QWORD PTR [rdi+1752]
	adc r12, QWORD PTR [rdi+1760]
	adc r13, QWORD PTR [rdi+1768]
	adc r14, QWORD PTR [rdi+1776]
	adc r15, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1720
	mov rbx, rdi
	add rbx, 1864
	call {vg_p521_win_mul_adx}
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq rbx, xmm7
	movq rsi, xmm6
	mov rbp, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+1800]
	mov r9, QWORD PTR [rdi+1808]
	mov r10, QWORD PTR [rdi+1816]
	mov r11, QWORD PTR [rdi+1824]
	mov r12, QWORD PTR [rdi+1832]
	mov r13, QWORD PTR [rdi+1840]
	mov r14, QWORD PTR [rdi+1848]
	mov r15, QWORD PTR [rdi+1856]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1720]
	adc r8, QWORD PTR [rdi+1728]
	adc r9, QWORD PTR [rdi+1736]
	adc r10, QWORD PTR [rdi+1744]
	adc r11, QWORD PTR [rdi+1752]
	adc r12, QWORD PTR [rdi+1760]
	adc r13, QWORD PTR [rdi+1768]
	adc r14, QWORD PTR [rdi+1776]
	adc r15, QWORD PTR [rdi+1784]
	add r15, 512
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	mov QWORD PTR [rdi+1144], rbp
	mov QWORD PTR [rdi+1152], r8
	mov QWORD PTR [rdi+1160], r9
	mov QWORD PTR [rdi+1168], r10
	mov QWORD PTR [rdi+1176], r11
	mov QWORD PTR [rdi+1184], r12
	mov QWORD PTR [rdi+1192], r13
	mov QWORD PTR [rdi+1200], r14
	mov QWORD PTR [rdi+1208], r15
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1216
	call {vg_p521_win_sqr_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq rbx, xmm7
	mov rbp, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+1728]
	mov r9, QWORD PTR [rdi+1736]
	mov r10, QWORD PTR [rdi+1744]
	mov r11, QWORD PTR [rdi+1752]
	mov r12, QWORD PTR [rdi+1760]
	mov r13, QWORD PTR [rdi+1768]
	mov r14, QWORD PTR [rdi+1776]
	mov r15, QWORD PTR [rdi+1784]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1072]
	adc r8, QWORD PTR [rdi+1080]
	adc r9, QWORD PTR [rdi+1088]
	adc r10, QWORD PTR [rdi+1096]
	adc r11, QWORD PTR [rdi+1104]
	adc r12, QWORD PTR [rdi+1112]
	adc r13, QWORD PTR [rdi+1120]
	adc r14, QWORD PTR [rdi+1128]
	adc r15, QWORD PTR [rdi+1136]
	add r15, 512
	mov QWORD PTR [rdi+1792], rbp
	mov QWORD PTR [rdi+1800], r8
	mov QWORD PTR [rdi+1808], r9
	mov QWORD PTR [rdi+1816], r10
	mov QWORD PTR [rdi+1824], r11
	mov QWORD PTR [rdi+1832], r12
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1144
	mov rbx, rdi
	add rbx, 1216
	call {vg_p521_win_mul_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1216], rbp
	mov QWORD PTR [rdi+1224], r8
	mov QWORD PTR [rdi+1232], r9
	mov QWORD PTR [rdi+1240], r10
	mov QWORD PTR [rdi+1248], r11
	mov QWORD PTR [rdi+1256], r12
	mov QWORD PTR [rdi+1264], r13
	mov QWORD PTR [rdi+1272], r14
	mov QWORD PTR [rdi+1280], r15
	movq rbx, xmm7
	movq rsi, xmm6
	mov rbp, QWORD PTR [rdi+1072]
	mov r8, QWORD PTR [rdi+1080]
	mov r9, QWORD PTR [rdi+1088]
	mov r10, QWORD PTR [rdi+1096]
	mov r11, QWORD PTR [rdi+1104]
	mov r12, QWORD PTR [rdi+1112]
	mov r13, QWORD PTR [rdi+1120]
	mov r14, QWORD PTR [rdi+1128]
	mov r15, QWORD PTR [rdi+1136]
	add rbp, QWORD PTR [rdi+1720]
	adc r8, QWORD PTR [rdi+1728]
	adc r9, QWORD PTR [rdi+1736]
	adc r10, QWORD PTR [rdi+1744]
	adc r11, QWORD PTR [rdi+1752]
	adc r12, QWORD PTR [rdi+1760]
	adc r13, QWORD PTR [rdi+1768]
	adc r14, QWORD PTR [rdi+1776]
	adc r15, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1792
	mov rbx, rdi
	add rbx, 1720
	call {vg_p521_win_mul_adx}
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq rbx, xmm7
	movq rsi, xmm6
	mov rbp, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+1728]
	mov r9, QWORD PTR [rdi+1736]
	mov r10, QWORD PTR [rdi+1744]
	mov r11, QWORD PTR [rdi+1752]
	mov r12, QWORD PTR [rdi+1760]
	mov r13, QWORD PTR [rdi+1768]
	mov r14, QWORD PTR [rdi+1776]
	mov r15, QWORD PTR [rdi+1784]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	add rbp, QWORD PTR [rdi+1720]
	adc r8, QWORD PTR [rdi+1728]
	adc r9, QWORD PTR [rdi+1736]
	adc r10, QWORD PTR [rdi+1744]
	adc r11, QWORD PTR [rdi+1752]
	adc r12, QWORD PTR [rdi+1760]
	adc r13, QWORD PTR [rdi+1768]
	adc r14, QWORD PTR [rdi+1776]
	adc r15, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1144
	call {vg_p521_win_sqr_adx}
	mov QWORD PTR [rdi+1792], rbp
	mov QWORD PTR [rdi+1800], r8
	mov QWORD PTR [rdi+1808], r9
	mov QWORD PTR [rdi+1816], r10
	mov QWORD PTR [rdi+1824], r11
	mov QWORD PTR [rdi+1832], r12
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	movq rbx, xmm7
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1072
	mov rbx, rdi
	add rbx, 1792
	call {vg_p521_win_mul_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1864], rbp
	mov QWORD PTR [rdi+1872], r8
	mov QWORD PTR [rdi+1880], r9
	mov QWORD PTR [rdi+1888], r10
	mov QWORD PTR [rdi+1896], r11
	mov QWORD PTR [rdi+1904], r12
	mov QWORD PTR [rdi+1912], r13
	mov QWORD PTR [rdi+1920], r14
	mov QWORD PTR [rdi+1928], r15
	movq rbx, xmm7
	movq rsi, xmm6
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1720
	call {vg_p521_win_sqr_adx}
	mov QWORD PTR [rdi+1936], rbp
	mov QWORD PTR [rdi+1944], r8
	mov QWORD PTR [rdi+1952], r9
	mov QWORD PTR [rdi+1960], r10
	mov QWORD PTR [rdi+1968], r11
	mov QWORD PTR [rdi+1976], r12
	mov QWORD PTR [rdi+1984], r13
	mov QWORD PTR [rdi+1992], r14
	mov QWORD PTR [rdi+2000], r15
	movq rbx, xmm7
	mov rbp, QWORD PTR [rdi+1864]
	mov r8, QWORD PTR [rdi+1872]
	mov r9, QWORD PTR [rdi+1880]
	mov r10, QWORD PTR [rdi+1888]
	mov r11, QWORD PTR [rdi+1896]
	mov r12, QWORD PTR [rdi+1904]
	mov r13, QWORD PTR [rdi+1912]
	mov r14, QWORD PTR [rdi+1920]
	mov r15, QWORD PTR [rdi+1928]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	add rbp, QWORD PTR [rdi+1936]
	adc r8, QWORD PTR [rdi+1944]
	adc r9, QWORD PTR [rdi+1952]
	adc r10, QWORD PTR [rdi+1960]
	adc r11, QWORD PTR [rdi+1968]
	adc r12, QWORD PTR [rdi+1976]
	adc r13, QWORD PTR [rdi+1984]
	adc r14, QWORD PTR [rdi+1992]
	adc r15, QWORD PTR [rdi+2000]
	add r15, 1024
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	mov QWORD PTR [rdi+1072], rbp
	mov QWORD PTR [rdi+1080], r8
	mov QWORD PTR [rdi+1088], r9
	mov QWORD PTR [rdi+1096], r10
	mov QWORD PTR [rdi+1104], r11
	mov QWORD PTR [rdi+1112], r12
	mov QWORD PTR [rdi+1120], r13
	mov QWORD PTR [rdi+1128], r14
	mov QWORD PTR [rdi+1136], r15
	movq xmm7, rbx
	mov rbx, rdi
	add rbx, 1792
	call {vg_p521_win_sqr_adx}
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov QWORD PTR [rdi+1792], rbp
	mov QWORD PTR [rdi+1800], r8
	mov QWORD PTR [rdi+1808], r9
	mov QWORD PTR [rdi+1816], r10
	mov QWORD PTR [rdi+1824], r11
	mov QWORD PTR [rdi+1832], r12
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	movq rbx, xmm7
	mov rbp, QWORD PTR [rdi+1072]
	mov r8, QWORD PTR [rdi+1080]
	mov r9, QWORD PTR [rdi+1088]
	mov r10, QWORD PTR [rdi+1096]
	mov r11, QWORD PTR [rdi+1104]
	mov r12, QWORD PTR [rdi+1112]
	mov r13, QWORD PTR [rdi+1120]
	mov r14, QWORD PTR [rdi+1128]
	mov r15, QWORD PTR [rdi+1136]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1864]
	adc r8, QWORD PTR [rdi+1872]
	adc r9, QWORD PTR [rdi+1880]
	adc r10, QWORD PTR [rdi+1888]
	adc r11, QWORD PTR [rdi+1896]
	adc r12, QWORD PTR [rdi+1904]
	adc r13, QWORD PTR [rdi+1912]
	adc r14, QWORD PTR [rdi+1920]
	adc r15, QWORD PTR [rdi+1928]
	add r15, 512
	mov QWORD PTR [rdi+1864], rbp
	mov QWORD PTR [rdi+1872], r8
	mov QWORD PTR [rdi+1880], r9
	mov QWORD PTR [rdi+1888], r10
	mov QWORD PTR [rdi+1896], r11
	mov QWORD PTR [rdi+1904], r12
	mov QWORD PTR [rdi+1912], r13
	mov QWORD PTR [rdi+1920], r14
	mov QWORD PTR [rdi+1928], r15
	mov rbp, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+1728]
	mov r9, QWORD PTR [rdi+1736]
	mov r10, QWORD PTR [rdi+1744]
	mov r11, QWORD PTR [rdi+1752]
	mov r12, QWORD PTR [rdi+1760]
	mov r13, QWORD PTR [rdi+1768]
	mov r14, QWORD PTR [rdi+1776]
	mov r15, QWORD PTR [rdi+1784]
	add rbp, QWORD PTR [rdi+1720]
	adc r8, QWORD PTR [rdi+1728]
	adc r9, QWORD PTR [rdi+1736]
	adc r10, QWORD PTR [rdi+1744]
	adc r11, QWORD PTR [rdi+1752]
	adc r12, QWORD PTR [rdi+1760]
	adc r13, QWORD PTR [rdi+1768]
	adc r14, QWORD PTR [rdi+1776]
	adc r15, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq xmm7, rbx
	movq xmm6, rsi
	mov rsi, rdi
	add rsi, 1720
	mov rbx, rdi
	add rbx, 1864
	call {vg_p521_win_mul_adx}
	mov QWORD PTR [rdi+1720], rbp
	mov QWORD PTR [rdi+1728], r8
	mov QWORD PTR [rdi+1736], r9
	mov QWORD PTR [rdi+1744], r10
	mov QWORD PTR [rdi+1752], r11
	mov QWORD PTR [rdi+1760], r12
	mov QWORD PTR [rdi+1768], r13
	mov QWORD PTR [rdi+1776], r14
	mov QWORD PTR [rdi+1784], r15
	movq rbx, xmm7
	movq rsi, xmm6
	mov rbp, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+1800]
	mov r9, QWORD PTR [rdi+1808]
	mov r10, QWORD PTR [rdi+1816]
	mov r11, QWORD PTR [rdi+1824]
	mov r12, QWORD PTR [rdi+1832]
	mov r13, QWORD PTR [rdi+1840]
	mov r14, QWORD PTR [rdi+1848]
	mov r15, QWORD PTR [rdi+1856]
	xor rbp, -1
	xor r8, -1
	xor r9, -1
	xor r10, -1
	xor r11, -1
	xor r12, -1
	xor r13, -1
	xor r14, -1
	xor r15, -1
	add rbp, QWORD PTR [rdi+1720]
	adc r8, QWORD PTR [rdi+1728]
	adc r9, QWORD PTR [rdi+1736]
	adc r10, QWORD PTR [rdi+1744]
	adc r11, QWORD PTR [rdi+1752]
	adc r12, QWORD PTR [rdi+1760]
	adc r13, QWORD PTR [rdi+1768]
	adc r14, QWORD PTR [rdi+1776]
	adc r15, QWORD PTR [rdi+1784]
	add r15, 512
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	adc r8, 0
	adc r9, 0
	adc r10, 0
	adc r11, 0
	adc r12, 0
	adc r13, 0
	adc r14, 0
	adc r15, 0
	mov rax, r15
	shr rax, 9
	and r15, 511
	add rbp, rax
	mov QWORD PTR [rdi+1144], rbp
	mov QWORD PTR [rdi+1152], r8
	mov QWORD PTR [rdi+1160], r9
	mov QWORD PTR [rdi+1168], r10
	mov QWORD PTR [rdi+1176], r11
	mov QWORD PTR [rdi+1184], r12
	mov QWORD PTR [rdi+1192], r13
	mov QWORD PTR [rdi+1200], r14
	mov QWORD PTR [rdi+1208], r15
	sub rbx, 4096
	cmp rbx, 4096
	jae 219b
	mov rbp, QWORD PTR [rdi+1144]
	mov r8, QWORD PTR [rdi+1152]
	mov r9, QWORD PTR [rdi+1160]
	mov r10, QWORD PTR [rdi+1168]
	mov r11, QWORD PTR [rdi+1176]
	mov r12, QWORD PTR [rdi+1184]
	mov r13, QWORD PTR [rdi+1192]
	mov r14, QWORD PTR [rdi+1200]
	mov r15, QWORD PTR [rdi+1208]
	mov rax, rbp
	and rax, 1
	shl rax, 8
	mov rcx, r15
	shr rcx, 1
	add rcx, rax
	shld r15, r14, 63
	shld r14, r13, 63
	shld r13, r12, 63
	shld r12, r11, 63
	shld r11, r10, 63
	shld r10, r9, 63
	shld r9, r8, 63
	shld r8, rbp, 63
	mov QWORD PTR [rdi+1144], r8
	mov QWORD PTR [rdi+1152], r9
	mov QWORD PTR [rdi+1160], r10
	mov QWORD PTR [rdi+1168], r11
	mov QWORD PTR [rdi+1176], r12
	mov QWORD PTR [rdi+1184], r13
	mov QWORD PTR [rdi+1192], r14
	mov QWORD PTR [rdi+1200], r15
	mov QWORD PTR [rdi+1208], rcx
	add rdi, 1144
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -864
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 864
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1144
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -792
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 792
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1072
	add rdi, 1216
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -936
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 936
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1216
	mov r12, rsi
	mov esi, 1288
	mov edx, 1072
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1432
	mov edx, 1720
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1144
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -864
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 1080
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+1280], rax
	mov rdx, QWORD PTR [rdi+1216]
	or rdx, QWORD PTR [rdi+1224]
	or rdx, QWORD PTR [rdi+1232]
	or rdx, QWORD PTR [rdi+1240]
	or rdx, QWORD PTR [rdi+1248]
	or rdx, QWORD PTR [rdi+1256]
	or rdx, QWORD PTR [rdi+1264]
	or rdx, QWORD PTR [rdi+1272]
	or rdx, QWORD PTR [rdi+1280]
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1144]
	movabs r8, 36028797018963968
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1152]
	movabs r8, 0
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1160]
	movabs r8, 0
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1168]
	movabs r8, 0
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1176]
	movabs r8, 0
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1184]
	movabs r8, 0
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1192]
	movabs r8, 0
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1200]
	movabs r8, 0
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1208]
	movabs r8, 0
	xor r8, rax
	and r8, rdx
	xor rax, r8
	mov QWORD PTR [rdi+1208], rax
	mov rax, rbx
	mov ecx, 4
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+5323]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+5322]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+5321]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+5320]
	add rax, rdx
	sub rax, 8
	mov rdx, rax
	shr rdx, 63
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	mov r8, rax
	mov rdx, rdi
	add rdx, 6112
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	mov ecx, 1
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+16]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+32]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+48]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+64]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+80]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+96]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+112]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+128]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+144]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+160]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+176]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+192]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+200]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 2
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+216]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+232]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+248]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+264]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+280]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+296]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+312]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+328]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+344]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+360]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+376]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+392]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+408]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+416]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 3
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+432]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+448]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+464]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+480]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+496]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+512]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+528]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+544]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+560]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+576]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+592]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+608]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+624]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+632]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 4
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+648]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+664]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+680]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+696]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+712]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+728]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+744]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+760]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+776]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+792]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+808]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+824]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+840]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+848]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 5
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+864]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+880]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+896]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+912]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+928]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+944]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+960]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+976]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+992]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1008]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1024]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1040]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1056]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1064]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 6
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1080]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1096]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1112]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1128]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1144]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1160]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1176]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1192]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1208]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1224]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1240]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1256]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1272]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1280]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 7
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1296]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1312]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1328]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1344]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1360]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1376]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1392]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1408]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1424]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1440]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1456]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1472]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1488]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1496]
	pand xmm14, xmm15
	por xmm13, xmm14
	mov ecx, 8
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1512]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1528]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1544]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1560]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1576]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1592]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1608]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1624]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1640]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1656]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1672]
	pand xmm14, xmm15
	por xmm10, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1688]
	pand xmm14, xmm15
	por xmm11, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1704]
	pand xmm14, xmm15
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1712]
	pand xmm14, xmm15
	por xmm13, xmm14
	movdqu XMMWORD PTR [rdi+1504], xmm0
	movdqu XMMWORD PTR [rdi+1520], xmm1
	movdqu XMMWORD PTR [rdi+1536], xmm2
	movdqu XMMWORD PTR [rdi+1552], xmm3
	movdqu XMMWORD PTR [rdi+1568], xmm4
	movdqu XMMWORD PTR [rdi+1584], xmm5
	movdqu XMMWORD PTR [rdi+1600], xmm6
	movdqu XMMWORD PTR [rdi+1616], xmm7
	movdqu XMMWORD PTR [rdi+1632], xmm8
	movdqu XMMWORD PTR [rdi+1648], xmm9
	movdqu XMMWORD PTR [rdi+1664], xmm10
	movdqu XMMWORD PTR [rdi+1680], xmm11
	movdqu XMMWORD PTR [rdi+1696], xmm12
	movdqu XMMWORD PTR [rdi+1704], xmm13
	mov rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movabs rax, 36028797018963968
	and rax, rcx
	or rax, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+1576], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+1584], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+1592], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+1600], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+1608], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+1616], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1624]
	mov QWORD PTR [rdi+1624], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1632]
	mov QWORD PTR [rdi+1632], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1640]
	mov QWORD PTR [rdi+1640], rax
	add rdi, 280
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 1296
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2224
	mov rax, rbx
	mov ecx, 4
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+5323]
	sub rax, 1
	mov rcx, rax
	mov rax, QWORD PTR [rdi+1576]
	mov rdx, QWORD PTR [rdi+2224]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rdi+1584]
	mov rdx, QWORD PTR [rdi+2232]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rdi+1592]
	mov rdx, QWORD PTR [rdi+2240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rdi+1600]
	mov rdx, QWORD PTR [rdi+2248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1600], rax
	mov rax, QWORD PTR [rdi+1608]
	mov rdx, QWORD PTR [rdi+2256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1608], rax
	mov rax, QWORD PTR [rdi+1616]
	mov rdx, QWORD PTR [rdi+2264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1616], rax
	mov rax, QWORD PTR [rdi+1624]
	mov rdx, QWORD PTR [rdi+2272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1624], rax
	mov rax, QWORD PTR [rdi+1632]
	mov rdx, QWORD PTR [rdi+2280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1632], rax
	mov rax, QWORD PTR [rdi+1640]
	mov rdx, QWORD PTR [rdi+2288]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1640], rax
	mov r12, rsi
	mov esi, 1720
	mov edx, 1072
	mov ecx, 1504
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1144
	mov ecx, 1576
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1216
	mov ecx, 1648
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 792
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1504
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 2008
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1144
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 792
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	add rdi, 1576
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 2008
	mov edx, 2008
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 2008
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -720
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 720
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1504
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -288
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1288
	mov edx, 1288
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1432
	mov edx, 2944
	mov ecx, 1864
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 144
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -504
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1360
	mov edx, 2944
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, -72
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 432
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -432
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 72
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1720
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1720
	mov r12, rsi
	mov esi, 1792
	mov edx, 2008
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1720
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1360
	mov edx, 1288
	mov ecx, 1432
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1432
	mov edx, 2008
	mov ecx, 1432
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1936
	mov ecx, 1720
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+1280], rax
	call {vg_p521_inv_mod_p}
	mov r12, rsi
	mov esi, 2512
	mov edx, 1072
	mov ecx, 2152
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2584
	mov edx, 2512
	mov ecx, 352
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov rdx, QWORD PTR [rdi+2368]
	sub rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2376]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2384]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2392]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2400]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2408]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2416]
	sbb rdx, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+2424]
	sbb rdx, QWORD PTR [rdi+192]
	mov rdx, QWORD PTR [rdi+2432]
	sbb rdx, QWORD PTR [rdi+200]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+2368]
	or rdx, QWORD PTR [rdi+2376]
	or rdx, QWORD PTR [rdi+2384]
	or rdx, QWORD PTR [rdi+2392]
	or rdx, QWORD PTR [rdi+2400]
	or rdx, QWORD PTR [rdi+2408]
	or rdx, QWORD PTR [rdi+2416]
	or rdx, QWORD PTR [rdi+2424]
	or rdx, QWORD PTR [rdi+2432]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+1216]
	or rdx, QWORD PTR [rdi+1224]
	or rdx, QWORD PTR [rdi+1232]
	or rdx, QWORD PTR [rdi+1240]
	or rdx, QWORD PTR [rdi+1248]
	or rdx, QWORD PTR [rdi+1256]
	or rdx, QWORD PTR [rdi+1264]
	or rdx, QWORD PTR [rdi+1272]
	or rdx, QWORD PTR [rdi+1280]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rcx, QWORD PTR [rdi+3232]
	mov rax, QWORD PTR [rdi+2584]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+58], rax
	mov rax, QWORD PTR [rdi+2592]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+50], rax
	mov rax, QWORD PTR [rdi+2600]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+42], rax
	mov rax, QWORD PTR [rdi+2608]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+34], rax
	mov rax, QWORD PTR [rdi+2616]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+26], rax
	mov rax, QWORD PTR [rdi+2624]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+18], rax
	mov rax, QWORD PTR [rdi+2632]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+10], rax
	mov rax, QWORD PTR [rdi+2640]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+2], rax
	mov rax, QWORD PTR [rdi+2648]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsi], dl
	mov rdx, rax
	mov BYTE PTR [rsi+1], dl
	mov rax, rcx
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6
