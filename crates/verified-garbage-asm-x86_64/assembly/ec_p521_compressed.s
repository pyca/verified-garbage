// The functions of `src/ec_p521_compressed.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p521_compress_public_key:
	mov r8, rdx
	mov r9, rsi
	mov rcx, rsi
	add rcx, 1
	mov rsi, rcx
	mov rdx, rcx
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
	mov rcx, QWORD PTR [rdi+3232]
	mov rdx, QWORD PTR [rdi+2656]
	and rdx, 1
	add rdx, 2
	and rdx, rcx
	mov BYTE PTR [rsi], dl
	mov rax, QWORD PTR [rdi+2440]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+59], rax
	mov rax, QWORD PTR [rdi+2448]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+51], rax
	mov rax, QWORD PTR [rdi+2456]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+43], rax
	mov rax, QWORD PTR [rdi+2464]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+35], rax
	mov rax, QWORD PTR [rdi+2472]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+27], rax
	mov rax, QWORD PTR [rdi+2480]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+19], rax
	mov rax, QWORD PTR [rdi+2488]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+11], rax
	mov rax, QWORD PTR [rdi+2496]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+3], rax
	mov rax, QWORD PTR [rdi+2504]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsi+1], dl
	mov rdx, rax
	mov BYTE PTR [rsi+2], dl
	mov rax, rcx
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6

vg_ec_p521_decompress_public_key:
	mov r8, rdx
	mov r9, rsi
	mov rcx, rsi
	add rcx, 1
	mov rsi, rcx
	mov rdx, rcx
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
	movzx edx, BYTE PTR [r9]
	mov QWORD PTR [rdi+2368], rdx
	and rdx, -2
	xor rdx, 2
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+2440]
	sub rdx, QWORD PTR [rdi+64]
	mov rdx, QWORD PTR [rdi+2448]
	sbb rdx, QWORD PTR [rdi+72]
	mov rdx, QWORD PTR [rdi+2456]
	sbb rdx, QWORD PTR [rdi+80]
	mov rdx, QWORD PTR [rdi+2464]
	sbb rdx, QWORD PTR [rdi+88]
	mov rdx, QWORD PTR [rdi+2472]
	sbb rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+2480]
	sbb rdx, QWORD PTR [rdi+104]
	mov rdx, QWORD PTR [rdi+2488]
	sbb rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+2496]
	sbb rdx, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+2504]
	sbb rdx, QWORD PTR [rdi+128]
	sbb rax, rax
	mov rdx, rax
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov r12, rsi
	mov esi, 2512
	mov edx, 2440
	mov ecx, 2872
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3016
	mov edx, 2512
	mov ecx, 2512
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3088
	mov edx, 3016
	mov ecx, 2512
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3016
	mov edx, 496
	mov ecx, 2512
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 3088
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
	sub rdi, 2800
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
	sub rdi, 3088
	movabs rax, 0
	mov QWORD PTR [rdi+928], rax
	movabs rax, 0
	mov QWORD PTR [rdi+936], rax
	movabs rax, 0
	mov QWORD PTR [rdi+944], rax
	movabs rax, 0
	mov QWORD PTR [rdi+952], rax
	movabs rax, 0
	mov QWORD PTR [rdi+960], rax
	movabs rax, 0
	mov QWORD PTR [rdi+968], rax
	movabs rax, 0
	mov QWORD PTR [rdi+976], rax
	movabs rax, 0
	mov QWORD PTR [rdi+984], rax
	movabs rax, 128
	mov QWORD PTR [rdi+992], rax
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+928]
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
	jne 20b
	mov rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+2152], rax
	mov rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+2160], rax
	mov rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+2168], rax
	mov rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+2176], rax
	mov rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+2184], rax
	mov rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+2192], rax
	mov rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+2200], rax
	mov rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+2208], rax
	mov rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+2216], rax
	mov ebx, 576
21:
	sub rbx, 1
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2152], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2160], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2168], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2176], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2184], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2192], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2200], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2208], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2216], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2152]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2152], rdx
	mov rdx, QWORD PTR [rdi+2160]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2160], rdx
	mov rdx, QWORD PTR [rdi+2168]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2168], rdx
	mov rdx, QWORD PTR [rdi+2176]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2176], rdx
	mov rdx, QWORD PTR [rdi+2184]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2184], rdx
	mov rdx, QWORD PTR [rdi+2192]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2192], rdx
	mov rdx, QWORD PTR [rdi+2200]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2200], rdx
	mov rdx, QWORD PTR [rdi+2208]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2208], rdx
	mov rdx, QWORD PTR [rdi+2216]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2216], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+3088]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+3096]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3088]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+3104]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3096]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3088]
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+3112]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3104]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3096]
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3088]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+3120]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3112]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3104]
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3096]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3088]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+3128]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3120]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3112]
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3104]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3096]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3088]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+3136]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3128]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3120]
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3112]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3104]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3096]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3088]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+3144]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3136]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3128]
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3120]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3112]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3104]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3096]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3088]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+3152]
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3144]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3136]
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3128]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3120]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3112]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3104]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3096]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3088]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+3152]
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3144]
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3136]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3128]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3120]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3112]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3104]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3096]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+3152]
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3144]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3136]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3128]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3120]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3112]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3104]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+3152]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3144]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3136]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3128]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3120]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3112]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+3152]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3144]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3136]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3128]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3120]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+3152]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3144]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3136]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3128]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+3152]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3144]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3136]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+3152]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3144]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+3152]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2224], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2232], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2240], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2248], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2256], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2264], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2272], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2280], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2288], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2224]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2224], rdx
	mov rdx, QWORD PTR [rdi+2232]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2232], rdx
	mov rdx, QWORD PTR [rdi+2240]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2240], rdx
	mov rdx, QWORD PTR [rdi+2248]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2248], rdx
	mov rdx, QWORD PTR [rdi+2256]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2256], rdx
	mov rdx, QWORD PTR [rdi+2264]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2264], rdx
	mov rdx, QWORD PTR [rdi+2272]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2272], rdx
	mov rdx, QWORD PTR [rdi+2280]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2280], rdx
	mov rdx, QWORD PTR [rdi+2288]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2288], rdx
	movzx eax, BYTE PTR [rdi+rbx*1+4472]
	mov ecx, 0
	sub rcx, rax
	mov rax, QWORD PTR [rdi+2152]
	mov rdx, QWORD PTR [rdi+2224]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2152], rax
	mov rax, QWORD PTR [rdi+2160]
	mov rdx, QWORD PTR [rdi+2232]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2160], rax
	mov rax, QWORD PTR [rdi+2168]
	mov rdx, QWORD PTR [rdi+2240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2168], rax
	mov rax, QWORD PTR [rdi+2176]
	mov rdx, QWORD PTR [rdi+2248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rax, QWORD PTR [rdi+2184]
	mov rdx, QWORD PTR [rdi+2256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2184], rax
	mov rax, QWORD PTR [rdi+2192]
	mov rdx, QWORD PTR [rdi+2264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2192], rax
	mov rax, QWORD PTR [rdi+2200]
	mov rdx, QWORD PTR [rdi+2272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2200], rax
	mov rax, QWORD PTR [rdi+2208]
	mov rdx, QWORD PTR [rdi+2280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2208], rax
	mov rax, QWORD PTR [rdi+2216]
	mov rdx, QWORD PTR [rdi+2288]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2216], rax
	test rbx, rbx
	jne 21b
	mov r12, rsi
	mov esi, 2656
	mov edx, 2152
	mov ecx, 352
	call {vg_p521_mul_mod_p}
	mov rsi, r12
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
	add rdi, 2376
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
	sub rdi, 2728
	mov rdx, QWORD PTR [rdi+2656]
	xor rdx, QWORD PTR [rdi+2368]
	and rdx, 1
	mov ecx, 0
	sub rcx, rdx
	mov rax, QWORD PTR [rdi+2656]
	mov rdx, QWORD PTR [rdi+2728]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2656], rax
	mov rax, QWORD PTR [rdi+2664]
	mov rdx, QWORD PTR [rdi+2736]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2664], rax
	mov rax, QWORD PTR [rdi+2672]
	mov rdx, QWORD PTR [rdi+2744]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2672], rax
	mov rax, QWORD PTR [rdi+2680]
	mov rdx, QWORD PTR [rdi+2752]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2680], rax
	mov rax, QWORD PTR [rdi+2688]
	mov rdx, QWORD PTR [rdi+2760]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2688], rax
	mov rax, QWORD PTR [rdi+2696]
	mov rdx, QWORD PTR [rdi+2768]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2696], rax
	mov rax, QWORD PTR [rdi+2704]
	mov rdx, QWORD PTR [rdi+2776]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2704], rax
	mov rax, QWORD PTR [rdi+2712]
	mov rdx, QWORD PTR [rdi+2784]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2712], rax
	mov rax, QWORD PTR [rdi+2720]
	mov rdx, QWORD PTR [rdi+2792]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2720], rax
	mov r12, rsi
	mov esi, 2584
	mov edx, 2656
	mov ecx, 2872
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3016
	mov edx, 2584
	mov ecx, 2584
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 3016
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
	sub rdi, 2800
	mov rdx, QWORD PTR [rdi+2800]
	or rdx, QWORD PTR [rdi+2808]
	or rdx, QWORD PTR [rdi+2816]
	or rdx, QWORD PTR [rdi+2824]
	or rdx, QWORD PTR [rdi+2832]
	or rdx, QWORD PTR [rdi+2840]
	or rdx, QWORD PTR [rdi+2848]
	or rdx, QWORD PTR [rdi+2856]
	or rdx, QWORD PTR [rdi+2864]
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+2656]
	xor rdx, QWORD PTR [rdi+2368]
	and rdx, 1
	mov ecx, 0
	sub rcx, rdx
	mov rdx, rcx
	xor rdx, -1
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rcx, QWORD PTR [rdi+3232]
	mov eax, 4
	and rax, rcx
	mov BYTE PTR [rsi], al
	mov rax, QWORD PTR [rdi+2440]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+59], rax
	mov rax, QWORD PTR [rdi+2448]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+51], rax
	mov rax, QWORD PTR [rdi+2456]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+43], rax
	mov rax, QWORD PTR [rdi+2464]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+35], rax
	mov rax, QWORD PTR [rdi+2472]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+27], rax
	mov rax, QWORD PTR [rdi+2480]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+19], rax
	mov rax, QWORD PTR [rdi+2488]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+11], rax
	mov rax, QWORD PTR [rdi+2496]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+3], rax
	mov rax, QWORD PTR [rdi+2504]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsi+1], dl
	mov rdx, rax
	mov BYTE PTR [rsi+2], dl
	mov rax, QWORD PTR [rdi+2656]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+125], rax
	mov rax, QWORD PTR [rdi+2664]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+117], rax
	mov rax, QWORD PTR [rdi+2672]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+109], rax
	mov rax, QWORD PTR [rdi+2680]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+101], rax
	mov rax, QWORD PTR [rdi+2688]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+93], rax
	mov rax, QWORD PTR [rdi+2696]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+85], rax
	mov rax, QWORD PTR [rdi+2704]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+77], rax
	mov rax, QWORD PTR [rdi+2712]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+69], rax
	mov rax, QWORD PTR [rdi+2720]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsi+67], dl
	mov rdx, rax
	mov BYTE PTR [rsi+68], dl
	mov rax, rcx
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6

vg_ec_p521_compress_public_key_adx:
	mov r8, rdx
	mov r9, rsi
	mov rcx, rsi
	add rcx, 1
	mov rsi, rcx
	mov rdx, rcx
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
	mov rcx, QWORD PTR [rdi+3232]
	mov rdx, QWORD PTR [rdi+2656]
	and rdx, 1
	add rdx, 2
	and rdx, rcx
	mov BYTE PTR [rsi], dl
	mov rax, QWORD PTR [rdi+2440]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+59], rax
	mov rax, QWORD PTR [rdi+2448]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+51], rax
	mov rax, QWORD PTR [rdi+2456]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+43], rax
	mov rax, QWORD PTR [rdi+2464]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+35], rax
	mov rax, QWORD PTR [rdi+2472]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+27], rax
	mov rax, QWORD PTR [rdi+2480]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+19], rax
	mov rax, QWORD PTR [rdi+2488]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+11], rax
	mov rax, QWORD PTR [rdi+2496]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+3], rax
	mov rax, QWORD PTR [rdi+2504]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsi+1], dl
	mov rdx, rax
	mov BYTE PTR [rsi+2], dl
	mov rax, rcx
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6

vg_ec_p521_decompress_public_key_adx:
	mov r8, rdx
	mov r9, rsi
	mov rcx, rsi
	add rcx, 1
	mov rsi, rcx
	mov rdx, rcx
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
	movzx edx, BYTE PTR [r9]
	mov QWORD PTR [rdi+2368], rdx
	and rdx, -2
	xor rdx, 2
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+2440]
	sub rdx, QWORD PTR [rdi+64]
	mov rdx, QWORD PTR [rdi+2448]
	sbb rdx, QWORD PTR [rdi+72]
	mov rdx, QWORD PTR [rdi+2456]
	sbb rdx, QWORD PTR [rdi+80]
	mov rdx, QWORD PTR [rdi+2464]
	sbb rdx, QWORD PTR [rdi+88]
	mov rdx, QWORD PTR [rdi+2472]
	sbb rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+2480]
	sbb rdx, QWORD PTR [rdi+104]
	mov rdx, QWORD PTR [rdi+2488]
	sbb rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+2496]
	sbb rdx, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+2504]
	sbb rdx, QWORD PTR [rdi+128]
	sbb rax, rax
	mov rdx, rax
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov r12, rsi
	mov esi, 2512
	mov edx, 2440
	mov ecx, 2872
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3016
	mov edx, 2512
	mov ecx, 2512
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3088
	mov edx, 3016
	mov ecx, 2512
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3016
	mov edx, 496
	mov ecx, 2512
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 3088
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
	sub rdi, 2800
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
	sub rdi, 3088
	movabs rax, 0
	mov QWORD PTR [rdi+928], rax
	movabs rax, 0
	mov QWORD PTR [rdi+936], rax
	movabs rax, 0
	mov QWORD PTR [rdi+944], rax
	movabs rax, 0
	mov QWORD PTR [rdi+952], rax
	movabs rax, 0
	mov QWORD PTR [rdi+960], rax
	movabs rax, 0
	mov QWORD PTR [rdi+968], rax
	movabs rax, 0
	mov QWORD PTR [rdi+976], rax
	movabs rax, 0
	mov QWORD PTR [rdi+984], rax
	movabs rax, 128
	mov QWORD PTR [rdi+992], rax
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+928]
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
	jne 20b
	mov rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+2152], rax
	mov rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+2160], rax
	mov rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+2168], rax
	mov rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+2176], rax
	mov rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+2184], rax
	mov rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+2192], rax
	mov rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+2200], rax
	mov rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+2208], rax
	mov rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+2216], rax
	mov ebx, 576
21:
	sub rbx, 1
	add rdi, 2152
	xor eax, eax
	mov QWORD PTR [rdi+1872], rax
	mov rdx, QWORD PTR [rdi]
	mulx r9, r8, QWORD PTR [rdi+8]
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov QWORD PTR [rdi+1880], r8
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+8]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov QWORD PTR [rdi+1888], r9
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+16]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov QWORD PTR [rdi+1896], r10
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+24]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov QWORD PTR [rdi+1904], r11
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+32]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov QWORD PTR [rdi+1912], r12
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+40]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov QWORD PTR [rdi+1920], r13
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+48]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov QWORD PTR [rdi+1928], r14
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+56]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov QWORD PTR [rdi+1936], r15
	mov r15d, 0
	xor eax, eax
	mov rdx, QWORD PTR [rdi]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+1872]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+1872], rdx
	mov rdx, QWORD PTR [rdi+1880]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+1880], rdx
	mov rdx, QWORD PTR [rdi+8]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+1888]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+1888], rdx
	mov rdx, QWORD PTR [rdi+1896]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+1896], rdx
	mov rdx, QWORD PTR [rdi+16]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+1904]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+1904], rdx
	mov rdx, QWORD PTR [rdi+1912]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+1912], rdx
	mov rdx, QWORD PTR [rdi+24]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+1920]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+1920], rdx
	mov rdx, QWORD PTR [rdi+1928]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+1928], rdx
	mov rdx, QWORD PTR [rdi+32]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+1936]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+1936], rdx
	adcx rbp, rbp
	adox rbp, rcx
	mov rdx, QWORD PTR [rdi+40]
	mulx rcx, rax, rdx
	adcx r8, r8
	adox r8, rax
	adcx r9, r9
	adox r9, rcx
	mov rdx, QWORD PTR [rdi+48]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+56]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+64]
	mulx rcx, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, r15
	adox r15, rcx
	add rdi, 1872
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -1872
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
	sub rdi, 2152
	add rdi, 3088
	mov rdx, QWORD PTR [rdi-936]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+936], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-928]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi+944], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-920]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+952], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-912]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+960], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-904]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+968], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-896]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+976], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-888]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi+984], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-880]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+992], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-872]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi+1000], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 936
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -1800
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
	movzx eax, BYTE PTR [rdi+rbx*1+4472]
	mov ecx, 0
	sub rcx, rax
	mov rax, QWORD PTR [rdi+2152]
	mov rdx, QWORD PTR [rdi+2224]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2152], rax
	mov rax, QWORD PTR [rdi+2160]
	mov rdx, QWORD PTR [rdi+2232]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2160], rax
	mov rax, QWORD PTR [rdi+2168]
	mov rdx, QWORD PTR [rdi+2240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2168], rax
	mov rax, QWORD PTR [rdi+2176]
	mov rdx, QWORD PTR [rdi+2248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rax, QWORD PTR [rdi+2184]
	mov rdx, QWORD PTR [rdi+2256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2184], rax
	mov rax, QWORD PTR [rdi+2192]
	mov rdx, QWORD PTR [rdi+2264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2192], rax
	mov rax, QWORD PTR [rdi+2200]
	mov rdx, QWORD PTR [rdi+2272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2200], rax
	mov rax, QWORD PTR [rdi+2208]
	mov rdx, QWORD PTR [rdi+2280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2208], rax
	mov rax, QWORD PTR [rdi+2216]
	mov rdx, QWORD PTR [rdi+2288]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2216], rax
	test rbx, rbx
	jne 21b
	mov r12, rsi
	mov esi, 2656
	mov edx, 2152
	mov ecx, 352
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
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
	add rdi, 2376
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
	sub rdi, 2728
	mov rdx, QWORD PTR [rdi+2656]
	xor rdx, QWORD PTR [rdi+2368]
	and rdx, 1
	mov ecx, 0
	sub rcx, rdx
	mov rax, QWORD PTR [rdi+2656]
	mov rdx, QWORD PTR [rdi+2728]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2656], rax
	mov rax, QWORD PTR [rdi+2664]
	mov rdx, QWORD PTR [rdi+2736]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2664], rax
	mov rax, QWORD PTR [rdi+2672]
	mov rdx, QWORD PTR [rdi+2744]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2672], rax
	mov rax, QWORD PTR [rdi+2680]
	mov rdx, QWORD PTR [rdi+2752]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2680], rax
	mov rax, QWORD PTR [rdi+2688]
	mov rdx, QWORD PTR [rdi+2760]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2688], rax
	mov rax, QWORD PTR [rdi+2696]
	mov rdx, QWORD PTR [rdi+2768]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2696], rax
	mov rax, QWORD PTR [rdi+2704]
	mov rdx, QWORD PTR [rdi+2776]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2704], rax
	mov rax, QWORD PTR [rdi+2712]
	mov rdx, QWORD PTR [rdi+2784]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2712], rax
	mov rax, QWORD PTR [rdi+2720]
	mov rdx, QWORD PTR [rdi+2792]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2720], rax
	mov r12, rsi
	mov esi, 2584
	mov edx, 2656
	mov ecx, 2872
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3016
	mov edx, 2584
	mov ecx, 2584
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 3016
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
	sub rdi, 2800
	mov rdx, QWORD PTR [rdi+2800]
	or rdx, QWORD PTR [rdi+2808]
	or rdx, QWORD PTR [rdi+2816]
	or rdx, QWORD PTR [rdi+2824]
	or rdx, QWORD PTR [rdi+2832]
	or rdx, QWORD PTR [rdi+2840]
	or rdx, QWORD PTR [rdi+2848]
	or rdx, QWORD PTR [rdi+2856]
	or rdx, QWORD PTR [rdi+2864]
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+2656]
	xor rdx, QWORD PTR [rdi+2368]
	and rdx, 1
	mov ecx, 0
	sub rcx, rdx
	mov rdx, rcx
	xor rdx, -1
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rcx, QWORD PTR [rdi+3232]
	mov eax, 4
	and rax, rcx
	mov BYTE PTR [rsi], al
	mov rax, QWORD PTR [rdi+2440]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+59], rax
	mov rax, QWORD PTR [rdi+2448]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+51], rax
	mov rax, QWORD PTR [rdi+2456]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+43], rax
	mov rax, QWORD PTR [rdi+2464]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+35], rax
	mov rax, QWORD PTR [rdi+2472]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+27], rax
	mov rax, QWORD PTR [rdi+2480]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+19], rax
	mov rax, QWORD PTR [rdi+2488]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+11], rax
	mov rax, QWORD PTR [rdi+2496]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+3], rax
	mov rax, QWORD PTR [rdi+2504]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsi+1], dl
	mov rdx, rax
	mov BYTE PTR [rsi+2], dl
	mov rax, QWORD PTR [rdi+2656]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+125], rax
	mov rax, QWORD PTR [rdi+2664]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+117], rax
	mov rax, QWORD PTR [rdi+2672]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+109], rax
	mov rax, QWORD PTR [rdi+2680]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+101], rax
	mov rax, QWORD PTR [rdi+2688]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+93], rax
	mov rax, QWORD PTR [rdi+2696]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+85], rax
	mov rax, QWORD PTR [rdi+2704]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+77], rax
	mov rax, QWORD PTR [rdi+2712]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+69], rax
	mov rax, QWORD PTR [rdi+2720]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsi+67], dl
	mov rdx, rax
	mov BYTE PTR [rsi+68], dl
	mov rax, rcx
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6
