// The functions of `src/ec_p521.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p521_public_key:
	mov r8, rdx
	mov rcx, rsi
	mov rdx, rsi
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
	jne 20b
	mov ebx, 0
21:
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
	jne 21b
	call {vg_p521_mul_base}
	call {vg_p521_inv_mod_p}
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1136]
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
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1136]
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
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1136]
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
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1136]
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
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1136]
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
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1136]
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
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1136]
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
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1136]
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
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1136]
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
	mov QWORD PTR [rdi+2512], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2520], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2528], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2536], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2544], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2552], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2560], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2568], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2576], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2512]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2512], rdx
	mov rdx, QWORD PTR [rdi+2520]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2520], rdx
	mov rdx, QWORD PTR [rdi+2528]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2528], rdx
	mov rdx, QWORD PTR [rdi+2536]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2536], rdx
	mov rdx, QWORD PTR [rdi+2544]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2544], rdx
	mov rdx, QWORD PTR [rdi+2552]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2552], rdx
	mov rdx, QWORD PTR [rdi+2560]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2560], rdx
	mov rdx, QWORD PTR [rdi+2568]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2568], rdx
	mov rdx, QWORD PTR [rdi+2576]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2576], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2576]
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
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2576]
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
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2576]
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
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2576]
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
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2576]
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
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2576]
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
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2576]
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
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2576]
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
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2576]
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
	mov QWORD PTR [rdi+2584], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2592], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2600], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2608], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2616], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2624], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2632], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2640], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2648], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2584]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2584], rdx
	mov rdx, QWORD PTR [rdi+2592]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2592], rdx
	mov rdx, QWORD PTR [rdi+2600]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2600], rdx
	mov rdx, QWORD PTR [rdi+2608]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2608], rdx
	mov rdx, QWORD PTR [rdi+2616]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2616], rdx
	mov rdx, QWORD PTR [rdi+2624]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2624], rdx
	mov rdx, QWORD PTR [rdi+2632]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2632], rdx
	mov rdx, QWORD PTR [rdi+2640]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2640], rdx
	mov rdx, QWORD PTR [rdi+2648]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2648], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1208]
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
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1208]
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
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1208]
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
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1208]
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
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1208]
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
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1208]
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
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1208]
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
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1208]
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
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1208]
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
	mov QWORD PTR [rdi+2800], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2808], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2816], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2824], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2832], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2840], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2848], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2856], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2864], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2800]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2800], rdx
	mov rdx, QWORD PTR [rdi+2808]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2808], rdx
	mov rdx, QWORD PTR [rdi+2816]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2816], rdx
	mov rdx, QWORD PTR [rdi+2824]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2824], rdx
	mov rdx, QWORD PTR [rdi+2832]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2832], rdx
	mov rdx, QWORD PTR [rdi+2840]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2840], rdx
	mov rdx, QWORD PTR [rdi+2848]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2848], rdx
	mov rdx, QWORD PTR [rdi+2856]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2856], rdx
	mov rdx, QWORD PTR [rdi+2864]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2864], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2800]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2800]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2808]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2800]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2808]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2816]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2800]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2808]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2816]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2824]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2800]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2808]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2816]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2824]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2832]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2800]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2808]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2816]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2824]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2832]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2840]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2800]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2808]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2816]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2824]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2832]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2840]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2848]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2800]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2808]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2816]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2824]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2832]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2840]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2848]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2800]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2808]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2816]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2824]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2832]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2840]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2848]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2864]
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
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2808]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2816]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2824]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2832]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2840]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2848]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2864]
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
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2816]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2824]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2832]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2840]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2848]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2864]
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
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2824]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2832]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2840]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2848]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2864]
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
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2832]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2840]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2848]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2864]
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
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2840]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2848]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2864]
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
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2848]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2864]
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
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2864]
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
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2864]
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
	mov QWORD PTR [rdi+3160], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3168], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3176], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3184], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3192], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3200], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3208], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3216], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3224], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+3160]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3160], rdx
	mov rdx, QWORD PTR [rdi+3168]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3168], rdx
	mov rdx, QWORD PTR [rdi+3176]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3176], rdx
	mov rdx, QWORD PTR [rdi+3184]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3184], rdx
	mov rdx, QWORD PTR [rdi+3192]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3192], rdx
	mov rdx, QWORD PTR [rdi+3200]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3200], rdx
	mov rdx, QWORD PTR [rdi+3208]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3208], rdx
	mov rdx, QWORD PTR [rdi+3216]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3216], rdx
	mov rdx, QWORD PTR [rdi+3224]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3224], rdx
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
	mov eax, 4
	and rax, rcx
	mov BYTE PTR [rsi], al
	mov rax, QWORD PTR [rdi+2584]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+59], rax
	mov rax, QWORD PTR [rdi+2592]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+51], rax
	mov rax, QWORD PTR [rdi+2600]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+43], rax
	mov rax, QWORD PTR [rdi+2608]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+35], rax
	mov rax, QWORD PTR [rdi+2616]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+27], rax
	mov rax, QWORD PTR [rdi+2624]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+19], rax
	mov rax, QWORD PTR [rdi+2632]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+11], rax
	mov rax, QWORD PTR [rdi+2640]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+3], rax
	mov rax, QWORD PTR [rdi+2648]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsi+1], dl
	mov rdx, rax
	mov BYTE PTR [rsi+2], dl
	mov rax, QWORD PTR [rdi+3160]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+125], rax
	mov rax, QWORD PTR [rdi+3168]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+117], rax
	mov rax, QWORD PTR [rdi+3176]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+109], rax
	mov rax, QWORD PTR [rdi+3184]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+101], rax
	mov rax, QWORD PTR [rdi+3192]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+93], rax
	mov rax, QWORD PTR [rdi+3200]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+85], rax
	mov rax, QWORD PTR [rdi+3208]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+77], rax
	mov rax, QWORD PTR [rdi+3216]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+69], rax
	mov rax, QWORD PTR [rdi+3224]
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+8]
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

vg_ec_p521_public_key_adx:
	mov r8, rdx
	mov rcx, rsi
	mov rdx, rsi
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
	jne 20b
	mov ebx, 0
21:
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
	jne 21b
	call {vg_p521_mul_base_adx}
	call {vg_p521_inv_mod_p}
	add rdi, 2152
	mov rdx, QWORD PTR [rdi-1080]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+1872], rax
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
	mov rdx, QWORD PTR [rdi-1072]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi+1880], r8
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
	mov rdx, QWORD PTR [rdi-1064]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+1888], r9
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
	mov rdx, QWORD PTR [rdi-1056]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+1896], r10
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
	mov rdx, QWORD PTR [rdi-1048]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+1904], r11
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
	mov rdx, QWORD PTR [rdi-1040]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+1912], r12
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
	mov rdx, QWORD PTR [rdi-1032]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi+1920], r13
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
	mov rdx, QWORD PTR [rdi-1024]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+1928], r14
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
	mov rdx, QWORD PTR [rdi-1016]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi+1936], r15
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
	add rdi, -1512
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
	sub rdi, 2512
	add rdi, 352
	mov rdx, QWORD PTR [rdi+2160]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3672], rax
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
	mov rdx, QWORD PTR [rdi+2168]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi+3680], r8
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
	mov rdx, QWORD PTR [rdi+2176]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+3688], r9
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
	mov rdx, QWORD PTR [rdi+2184]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+3696], r10
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
	mov rdx, QWORD PTR [rdi+2192]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+3704], r11
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
	mov rdx, QWORD PTR [rdi+2200]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+3712], r12
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
	mov rdx, QWORD PTR [rdi+2208]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi+3720], r13
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
	mov rdx, QWORD PTR [rdi+2216]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+3728], r14
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
	mov rdx, QWORD PTR [rdi+2224]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi+3736], r15
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
	add rdi, 3672
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
	add rdi, -1440
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
	sub rdi, 2584
	add rdi, 2152
	mov rdx, QWORD PTR [rdi-1008]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+1872], rax
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
	mov rdx, QWORD PTR [rdi-1000]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi+1880], r8
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
	mov rdx, QWORD PTR [rdi-992]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+1888], r9
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
	mov rdx, QWORD PTR [rdi-984]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+1896], r10
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
	mov rdx, QWORD PTR [rdi-976]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+1904], r11
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
	mov rdx, QWORD PTR [rdi-968]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+1912], r12
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
	mov rdx, QWORD PTR [rdi-960]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi+1920], r13
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
	mov rdx, QWORD PTR [rdi-952]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+1928], r14
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
	mov rdx, QWORD PTR [rdi-944]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi+1936], r15
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
	add rdi, -1224
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
	add rdi, 352
	mov rdx, QWORD PTR [rdi+2448]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3672], rax
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
	mov rdx, QWORD PTR [rdi+2456]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi+3680], r8
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
	mov rdx, QWORD PTR [rdi+2464]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+3688], r9
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
	mov rdx, QWORD PTR [rdi+2472]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+3696], r10
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
	mov rdx, QWORD PTR [rdi+2480]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+3704], r11
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
	mov rdx, QWORD PTR [rdi+2488]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+3712], r12
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
	mov rdx, QWORD PTR [rdi+2496]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi+3720], r13
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
	mov rdx, QWORD PTR [rdi+2504]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+3728], r14
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
	mov rdx, QWORD PTR [rdi+2512]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi+3736], r15
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
	add rdi, 3672
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
	add rdi, -864
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
	sub rdi, 3160
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
	mov eax, 4
	and rax, rcx
	mov BYTE PTR [rsi], al
	mov rax, QWORD PTR [rdi+2584]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+59], rax
	mov rax, QWORD PTR [rdi+2592]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+51], rax
	mov rax, QWORD PTR [rdi+2600]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+43], rax
	mov rax, QWORD PTR [rdi+2608]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+35], rax
	mov rax, QWORD PTR [rdi+2616]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+27], rax
	mov rax, QWORD PTR [rdi+2624]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+19], rax
	mov rax, QWORD PTR [rdi+2632]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+11], rax
	mov rax, QWORD PTR [rdi+2640]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+3], rax
	mov rax, QWORD PTR [rdi+2648]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsi+1], dl
	mov rdx, rax
	mov BYTE PTR [rsi+2], dl
	mov rax, QWORD PTR [rdi+3160]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+125], rax
	mov rax, QWORD PTR [rdi+3168]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+117], rax
	mov rax, QWORD PTR [rdi+3176]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+109], rax
	mov rax, QWORD PTR [rdi+3184]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+101], rax
	mov rax, QWORD PTR [rdi+3192]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+93], rax
	mov rax, QWORD PTR [rdi+3200]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+85], rax
	mov rax, QWORD PTR [rdi+3208]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+77], rax
	mov rax, QWORD PTR [rdi+3216]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+69], rax
	mov rax, QWORD PTR [rdi+3224]
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
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+8]
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
