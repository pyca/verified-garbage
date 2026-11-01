// The functions of `src/ecdsa_brainpoolp512r1.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp512r1_sign:
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r14, rdi
	mov rdi, r8
	mov rax, QWORD PTR [rcx+56]
	bswap rax
	mov QWORD PTR [rdi+2048], rax
	mov rax, QWORD PTR [rcx+48]
	bswap rax
	mov QWORD PTR [rdi+2056], rax
	mov rax, QWORD PTR [rcx+40]
	bswap rax
	mov QWORD PTR [rdi+2064], rax
	mov rax, QWORD PTR [rcx+32]
	bswap rax
	mov QWORD PTR [rdi+2072], rax
	mov rax, QWORD PTR [rcx+24]
	bswap rax
	mov QWORD PTR [rdi+2080], rax
	mov rax, QWORD PTR [rcx+16]
	bswap rax
	mov QWORD PTR [rdi+2088], rax
	mov rax, QWORD PTR [rcx+8]
	bswap rax
	mov QWORD PTR [rdi+2096], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	mov QWORD PTR [rdi+2104], rax
	mov rax, QWORD PTR [rsi+56]
	bswap rax
	mov QWORD PTR [rdi+2112], rax
	mov rax, QWORD PTR [rsi+48]
	bswap rax
	mov QWORD PTR [rdi+2120], rax
	mov rax, QWORD PTR [rsi+40]
	bswap rax
	mov QWORD PTR [rdi+2128], rax
	mov rax, QWORD PTR [rsi+32]
	bswap rax
	mov QWORD PTR [rdi+2136], rax
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rdi+2144], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rdi+2152], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rdi+2160], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rdi+2168], rax
	mov rax, QWORD PTR [rdx+56]
	bswap rax
	mov QWORD PTR [rdi+2176], rax
	mov rax, QWORD PTR [rdx+48]
	bswap rax
	mov QWORD PTR [rdi+2184], rax
	mov rax, QWORD PTR [rdx+40]
	bswap rax
	mov QWORD PTR [rdi+2192], rax
	mov rax, QWORD PTR [rdx+32]
	bswap rax
	mov QWORD PTR [rdi+2200], rax
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+2208], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+2216], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+2224], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+2232], rax
	movabs rax, 2930260431521597683
	mov QWORD PTR [rdi+64], rax
	movabs rax, 2918894611604883077
	mov QWORD PTR [rdi+72], rax
	movabs rax, -5850843135254232858
	mov QWORD PTR [rdi+80], rax
	movabs rax, 9029043254863489090
	mov QWORD PTR [rdi+88], rax
	movabs rax, -2998380533618898831
	mov QWORD PTR [rdi+96], rax
	movabs rax, -3805385882173058546
	mov QWORD PTR [rdi+104], rax
	movabs rax, 4599554755319692295
	mov QWORD PTR [rdi+112], rax
	movabs rax, -6134573700119673717
	mov QWORD PTR [rdi+120], rax
	movabs rax, -5366154943270420375
	mov QWORD PTR [rdi+128], rax
	movabs rax, 2139723849122306781
	mov QWORD PTR [rdi+136], rax
	movabs rax, 4721568021488603207
	mov QWORD PTR [rdi+144], rax
	movabs rax, 6142448377308718617
	mov QWORD PTR [rdi+152], rax
	movabs rax, -2998380533618898832
	mov QWORD PTR [rdi+160], rax
	movabs rax, -3805385882173058546
	mov QWORD PTR [rdi+168], rax
	movabs rax, 4599554755319692295
	mov QWORD PTR [rdi+176], rax
	movabs rax, -6134573700119673717
	mov QWORD PTR [rdi+184], rax
	movabs rax, 0
	mov QWORD PTR [rdi+256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+272], rax
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
	movabs rax, 1
	mov QWORD PTR [rdi+320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+344], rax
	movabs rax, 0
	mov QWORD PTR [rdi+352], rax
	movabs rax, 0
	mov QWORD PTR [rdi+360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+376], rax
	movabs rax, -2930260431521597683
	mov QWORD PTR [rdi+384], rax
	movabs rax, -2918894611604883078
	mov QWORD PTR [rdi+392], rax
	movabs rax, 5850843135254232857
	mov QWORD PTR [rdi+400], rax
	movabs rax, -9029043254863489091
	mov QWORD PTR [rdi+408], rax
	movabs rax, 2998380533618898830
	mov QWORD PTR [rdi+416], rax
	movabs rax, 3805385882173058545
	mov QWORD PTR [rdi+424], rax
	movabs rax, -4599554755319692296
	mov QWORD PTR [rdi+432], rax
	movabs rax, 6134573700119673716
	mov QWORD PTR [rdi+440], rax
	movabs rax, -2729310889293331386
	mov QWORD PTR [rdi+448], rax
	movabs rax, 1505492542499050115
	mov QWORD PTR [rdi+456], rax
	movabs rax, 4661308568508939179
	mov QWORD PTR [rdi+464], rax
	movabs rax, -3490570011004729345
	mov QWORD PTR [rdi+472], rax
	movabs rax, -6490759326330727993
	mov QWORD PTR [rdi+480], rax
	movabs rax, 1742065509884397432
	mov QWORD PTR [rdi+488], rax
	movabs rax, -5171393534022875892
	mov QWORD PTR [rdi+496], rax
	movabs rax, 6828848497702021763
	mov QWORD PTR [rdi+504], rax
	movabs rax, -3976350352470362711
	mov QWORD PTR [rdi+512], rax
	movabs rax, -2787679616831567849
	mov QWORD PTR [rdi+520], rax
	movabs rax, -759617572635022057
	mov QWORD PTR [rdi+528], rax
	movabs rax, -2851632089325841979
	mov QWORD PTR [rdi+536], rax
	movabs rax, -1063825459454450647
	mov QWORD PTR [rdi+544], rax
	movabs rax, -7467397740859902391
	mov QWORD PTR [rdi+552], rax
	movabs rax, -1399404244870167584
	mov QWORD PTR [rdi+560], rax
	movabs rax, -7781545726081636502
	mov QWORD PTR [rdi+568], rax
	movabs rax, -4265306830309041709
	mov QWORD PTR [rdi+576], rax
	movabs rax, 7511526321049830052
	mov QWORD PTR [rdi+584], rax
	movabs rax, 3795131596780428943
	mov QWORD PTR [rdi+592], rax
	movabs rax, -8840474168764915768
	mov QWORD PTR [rdi+600], rax
	movabs rax, 2608665483340973879
	mov QWORD PTR [rdi+608], rax
	movabs rax, -5569006363168916233
	mov QWORD PTR [rdi+616], rax
	movabs rax, -8710887700046199437
	mov QWORD PTR [rdi+624], rax
	movabs rax, 6497464235362412929
	mov QWORD PTR [rdi+632], rax
	movabs rax, 3427351643329669741
	mov QWORD PTR [rdi+640], rax
	movabs rax, 8437739570908558117
	mov QWORD PTR [rdi+648], rax
	movabs rax, -4646495099285039984
	mov QWORD PTR [rdi+656], rax
	movabs rax, 3895270034549689406
	mov QWORD PTR [rdi+664], rax
	movabs rax, 8941628266325094364
	mov QWORD PTR [rdi+672], rax
	movabs rax, 6367293241722486668
	mov QWORD PTR [rdi+680], rax
	movabs rax, -7323178610489081957
	mov QWORD PTR [rdi+688], rax
	movabs rax, -8335941010059464063
	mov QWORD PTR [rdi+696], rax
	movabs rax, -3268654423032195471
	mov QWORD PTR [rdi+704], rax
	movabs rax, 614379990270098909
	mov QWORD PTR [rdi+712], rax
	movabs rax, 4523386233333179007
	mov QWORD PTR [rdi+720], rax
	movabs rax, -6417012887004248088
	mov QWORD PTR [rdi+728], rax
	movabs rax, -2884049621775479325
	mov QWORD PTR [rdi+736], rax
	movabs rax, 8231515388640672735
	mov QWORD PTR [rdi+744], rax
	movabs rax, -7647363628595990954
	mov QWORD PTR [rdi+752], rax
	movabs rax, -6371370358628153424
	mov QWORD PTR [rdi+760], rax
	movabs rax, 5366154943270420375
	mov QWORD PTR [rdi+768], rax
	movabs rax, -2139723849122306782
	mov QWORD PTR [rdi+776], rax
	movabs rax, -4721568021488603208
	mov QWORD PTR [rdi+784], rax
	movabs rax, -6142448377308718618
	mov QWORD PTR [rdi+792], rax
	movabs rax, 2998380533618898831
	mov QWORD PTR [rdi+800], rax
	movabs rax, 3805385882173058545
	mov QWORD PTR [rdi+808], rax
	movabs rax, -4599554755319692296
	mov QWORD PTR [rdi+816], rax
	movabs rax, 6134573700119673716
	mov QWORD PTR [rdi+824], rax
	movabs rax, 2930260431521597681
	mov QWORD PTR [rdi+832], rax
	movabs rax, 2918894611604883077
	mov QWORD PTR [rdi+840], rax
	movabs rax, -5850843135254232858
	mov QWORD PTR [rdi+848], rax
	movabs rax, 9029043254863489090
	mov QWORD PTR [rdi+856], rax
	movabs rax, -2998380533618898831
	mov QWORD PTR [rdi+864], rax
	movabs rax, -3805385882173058546
	mov QWORD PTR [rdi+872], rax
	movabs rax, 4599554755319692295
	mov QWORD PTR [rdi+880], rax
	movabs rax, -6134573700119673717
	mov QWORD PTR [rdi+888], rax
	movabs rax, -5366154943270420377
	mov QWORD PTR [rdi+896], rax
	movabs rax, 2139723849122306781
	mov QWORD PTR [rdi+904], rax
	movabs rax, 4721568021488603207
	mov QWORD PTR [rdi+912], rax
	movabs rax, 6142448377308718617
	mov QWORD PTR [rdi+920], rax
	movabs rax, -2998380533618898832
	mov QWORD PTR [rdi+928], rax
	movabs rax, -3805385882173058546
	mov QWORD PTR [rdi+936], rax
	movabs rax, 4599554755319692295
	mov QWORD PTR [rdi+944], rax
	movabs rax, -6134573700119673717
	mov QWORD PTR [rdi+952], rax
	movabs rax, 0
	mov QWORD PTR [rdi+960], rax
	movabs rax, 0
	mov QWORD PTR [rdi+968], rax
	movabs rax, 0
	mov QWORD PTR [rdi+976], rax
	movabs rax, 0
	mov QWORD PTR [rdi+984], rax
	movabs rax, 0
	mov QWORD PTR [rdi+992], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1000], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1008], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1016], rax
	movabs rax, -2930260431521597683
	mov QWORD PTR [rdi+1024], rax
	movabs rax, -2918894611604883078
	mov QWORD PTR [rdi+1032], rax
	movabs rax, 5850843135254232857
	mov QWORD PTR [rdi+1040], rax
	movabs rax, -9029043254863489091
	mov QWORD PTR [rdi+1048], rax
	movabs rax, 2998380533618898830
	mov QWORD PTR [rdi+1056], rax
	movabs rax, 3805385882173058545
	mov QWORD PTR [rdi+1064], rax
	movabs rax, -4599554755319692296
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 6134573700119673716
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
	movabs rax, 0
	mov QWORD PTR [rdi+1144], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2880], rax
	mov rsi, r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+832]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3464], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3465], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3466], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3467], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3468], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3469], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3470], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3471], dl
	add rbx, 1
	cmp rbx, 64
	jne 20b
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rdi+rbx*1+896]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3984], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3985], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3986], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3987], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3988], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3989], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3990], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3991], dl
	add rbx, 1
	cmp rbx, 64
	jne 21b
	mov rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+1016], rax
	mov rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+1024], rax
	mov rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+1032], rax
	mov rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+1040], rax
	mov rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+1048], rax
	mov rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+1080], rax
	call {vg_brainpoolp512r1_mul}
	call {vg_brainpoolp512r1_inv_mod_p}
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2240], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2248], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2256], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2264], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2272], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2280], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2288], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2296], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2240]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2240], rdx
	mov rdx, QWORD PTR [rdi+2248]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2248], rdx
	mov rdx, QWORD PTR [rdi+2256]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2256], rdx
	mov rdx, QWORD PTR [rdi+2264]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2264], rdx
	mov rdx, QWORD PTR [rdi+2272]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2272], rdx
	mov rdx, QWORD PTR [rdi+2280]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2280], rdx
	mov rdx, QWORD PTR [rdi+2288]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2288], rdx
	mov rdx, QWORD PTR [rdi+2296]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2296], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+320]
	mov rax, QWORD PTR [rdi+2240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+328]
	mov rax, QWORD PTR [rdi+2240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+320]
	mov rax, QWORD PTR [rdi+2248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+336]
	mov rax, QWORD PTR [rdi+2240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+328]
	mov rax, QWORD PTR [rdi+2248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+320]
	mov rax, QWORD PTR [rdi+2256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+344]
	mov rax, QWORD PTR [rdi+2240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+336]
	mov rax, QWORD PTR [rdi+2248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+328]
	mov rax, QWORD PTR [rdi+2256]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+320]
	mov rax, QWORD PTR [rdi+2264]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+344]
	mov rax, QWORD PTR [rdi+2248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+336]
	mov rax, QWORD PTR [rdi+2256]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+328]
	mov rax, QWORD PTR [rdi+2264]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+320]
	mov rax, QWORD PTR [rdi+2272]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+344]
	mov rax, QWORD PTR [rdi+2256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+336]
	mov rax, QWORD PTR [rdi+2264]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+328]
	mov rax, QWORD PTR [rdi+2272]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+320]
	mov rax, QWORD PTR [rdi+2280]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2256]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+344]
	mov rax, QWORD PTR [rdi+2264]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+336]
	mov rax, QWORD PTR [rdi+2272]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+328]
	mov rax, QWORD PTR [rdi+2280]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+320]
	mov rax, QWORD PTR [rdi+2288]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2256]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2264]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+344]
	mov rax, QWORD PTR [rdi+2272]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+336]
	mov rax, QWORD PTR [rdi+2280]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+328]
	mov rax, QWORD PTR [rdi+2288]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+320]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2264]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2272]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+344]
	mov rax, QWORD PTR [rdi+2280]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+336]
	mov rax, QWORD PTR [rdi+2288]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+328]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2256]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2264]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2272]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2280]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+344]
	mov rax, QWORD PTR [rdi+2288]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+336]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2264]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2272]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2280]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2288]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+344]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2272]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2280]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2288]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2280]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2288]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2288]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2304], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2312], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2320], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2328], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2336], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2344], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2352], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2360], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2304]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2304], rdx
	mov rdx, QWORD PTR [rdi+2312]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2312], rdx
	mov rdx, QWORD PTR [rdi+2320]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2320], rdx
	mov rdx, QWORD PTR [rdi+2328]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2328], rdx
	mov rdx, QWORD PTR [rdi+2336]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2336], rdx
	mov rdx, QWORD PTR [rdi+2344]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2344], rdx
	mov rdx, QWORD PTR [rdi+2352]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2352], rdx
	mov rdx, QWORD PTR [rdi+2360]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2360], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+2304]
	add r8, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+2312]
	adc r8, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+2320]
	adc r8, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+2328]
	adc r8, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+2336]
	adc r8, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+2344]
	adc r8, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+2352]
	adc r8, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+2360]
	adc r8, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2368], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+2376], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+2384], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+2392], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+2400], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+2408], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+2416], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+2424], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2368]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2368], rdx
	mov rdx, QWORD PTR [rdi+2376]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2376], rdx
	mov rdx, QWORD PTR [rdi+2384]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2384], rdx
	mov rdx, QWORD PTR [rdi+2392]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2392], rdx
	mov rdx, QWORD PTR [rdi+2400]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2400], rdx
	mov rdx, QWORD PTR [rdi+2408]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2408], rdx
	mov rdx, QWORD PTR [rdi+2416]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2416], rdx
	mov rdx, QWORD PTR [rdi+2424]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2424], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+704]
	mov rax, QWORD PTR [rdi+2048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -5960140139473965017
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+712]
	mov rax, QWORD PTR [rdi+2048]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+704]
	mov rax, QWORD PTR [rdi+2056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+136]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -5960140139473965017
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+720]
	mov rax, QWORD PTR [rdi+2048]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+712]
	mov rax, QWORD PTR [rdi+2056]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+704]
	mov rax, QWORD PTR [rdi+2064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+136]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -5960140139473965017
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+2048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+720]
	mov rax, QWORD PTR [rdi+2056]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+712]
	mov rax, QWORD PTR [rdi+2064]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+704]
	mov rax, QWORD PTR [rdi+2072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+136]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -5960140139473965017
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+736]
	mov rax, QWORD PTR [rdi+2048]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+2056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+720]
	mov rax, QWORD PTR [rdi+2064]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+712]
	mov rax, QWORD PTR [rdi+2072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+704]
	mov rax, QWORD PTR [rdi+2080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+136]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -5960140139473965017
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+744]
	mov rax, QWORD PTR [rdi+2048]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+736]
	mov rax, QWORD PTR [rdi+2056]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+2064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+720]
	mov rax, QWORD PTR [rdi+2072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+712]
	mov rax, QWORD PTR [rdi+2080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+704]
	mov rax, QWORD PTR [rdi+2088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+136]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -5960140139473965017
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+752]
	mov rax, QWORD PTR [rdi+2048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+744]
	mov rax, QWORD PTR [rdi+2056]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+736]
	mov rax, QWORD PTR [rdi+2064]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+2072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+720]
	mov rax, QWORD PTR [rdi+2080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+712]
	mov rax, QWORD PTR [rdi+2088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+704]
	mov rax, QWORD PTR [rdi+2096]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+136]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -5960140139473965017
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+760]
	mov rax, QWORD PTR [rdi+2048]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+752]
	mov rax, QWORD PTR [rdi+2056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+744]
	mov rax, QWORD PTR [rdi+2064]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+736]
	mov rax, QWORD PTR [rdi+2072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+2080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+720]
	mov rax, QWORD PTR [rdi+2088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+712]
	mov rax, QWORD PTR [rdi+2096]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+704]
	mov rax, QWORD PTR [rdi+2104]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+136]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -5960140139473965017
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+760]
	mov rax, QWORD PTR [rdi+2056]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+752]
	mov rax, QWORD PTR [rdi+2064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+744]
	mov rax, QWORD PTR [rdi+2072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+736]
	mov rax, QWORD PTR [rdi+2080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+2088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+720]
	mov rax, QWORD PTR [rdi+2096]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+712]
	mov rax, QWORD PTR [rdi+2104]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+136]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+760]
	mov rax, QWORD PTR [rdi+2064]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+752]
	mov rax, QWORD PTR [rdi+2072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+744]
	mov rax, QWORD PTR [rdi+2080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+736]
	mov rax, QWORD PTR [rdi+2088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+2096]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+720]
	mov rax, QWORD PTR [rdi+2104]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+760]
	mov rax, QWORD PTR [rdi+2072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+752]
	mov rax, QWORD PTR [rdi+2080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+744]
	mov rax, QWORD PTR [rdi+2088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+736]
	mov rax, QWORD PTR [rdi+2096]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+2104]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+760]
	mov rax, QWORD PTR [rdi+2080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+752]
	mov rax, QWORD PTR [rdi+2088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+744]
	mov rax, QWORD PTR [rdi+2096]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+736]
	mov rax, QWORD PTR [rdi+2104]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+760]
	mov rax, QWORD PTR [rdi+2088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+752]
	mov rax, QWORD PTR [rdi+2096]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+744]
	mov rax, QWORD PTR [rdi+2104]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+760]
	mov rax, QWORD PTR [rdi+2096]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+752]
	mov rax, QWORD PTR [rdi+2104]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+760]
	mov rax, QWORD PTR [rdi+2104]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2432], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+2440], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+2448], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+2456], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+2464], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+2472], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+2480], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+2488], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2432]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2432], rdx
	mov rdx, QWORD PTR [rdi+2440]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2440], rdx
	mov rdx, QWORD PTR [rdi+2448]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2448], rdx
	mov rdx, QWORD PTR [rdi+2456]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2456], rdx
	mov rdx, QWORD PTR [rdi+2464]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2464], rdx
	mov rdx, QWORD PTR [rdi+2472]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2472], rdx
	mov rdx, QWORD PTR [rdi+2480]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2480], rdx
	mov rdx, QWORD PTR [rdi+2488]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2488], rdx
	mov rdx, QWORD PTR [rdi+2112]
	sub rdx, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rdi+2120]
	sbb rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2128]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2136]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2144]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2152]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2160]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2168]
	sbb rdx, QWORD PTR [rdi+184]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+2112]
	or rdx, QWORD PTR [rdi+2120]
	or rdx, QWORD PTR [rdi+2128]
	or rdx, QWORD PTR [rdi+2136]
	or rdx, QWORD PTR [rdi+2144]
	or rdx, QWORD PTR [rdi+2152]
	or rdx, QWORD PTR [rdi+2160]
	or rdx, QWORD PTR [rdi+2168]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+2880]
	and rax, rdx
	mov QWORD PTR [rdi+2880], rax
	mov rdx, QWORD PTR [rdi+2048]
	sub rdx, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rdi+2056]
	sbb rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2064]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2072]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2080]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2088]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2096]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2104]
	sbb rdx, QWORD PTR [rdi+184]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+2048]
	or rdx, QWORD PTR [rdi+2056]
	or rdx, QWORD PTR [rdi+2064]
	or rdx, QWORD PTR [rdi+2072]
	or rdx, QWORD PTR [rdi+2080]
	or rdx, QWORD PTR [rdi+2088]
	or rdx, QWORD PTR [rdi+2096]
	or rdx, QWORD PTR [rdi+2104]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+2880]
	and rax, rdx
	mov QWORD PTR [rdi+2880], rax
	mov rdx, QWORD PTR [rdi+2368]
	or rdx, QWORD PTR [rdi+2376]
	or rdx, QWORD PTR [rdi+2384]
	or rdx, QWORD PTR [rdi+2392]
	or rdx, QWORD PTR [rdi+2400]
	or rdx, QWORD PTR [rdi+2408]
	or rdx, QWORD PTR [rdi+2416]
	or rdx, QWORD PTR [rdi+2424]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2880]
	and rax, rdx
	mov QWORD PTR [rdi+2880], rax
	call {vg_brainpoolp512r1_inv_mod_n}
	mov r12, rsi
	mov esi, 2496
	mov edx, 2368
	mov ecx, 704
	call {vg_brainpoolp512r1_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2560
	mov edx, 2112
	mov ecx, 704
	call {vg_brainpoolp512r1_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2624
	mov edx, 2176
	mov ecx, 704
	call {vg_brainpoolp512r1_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2688
	mov edx, 2496
	mov ecx, 2560
	call {vg_brainpoolp512r1_mul_mod_n}
	mov rsi, r12
	mov r9d, 0
	mov r8, QWORD PTR [rdi+2688]
	add r8, QWORD PTR [rdi+2624]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+2696]
	adc r8, QWORD PTR [rdi+2632]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+2704]
	adc r8, QWORD PTR [rdi+2640]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+2712]
	adc r8, QWORD PTR [rdi+2648]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+2720]
	adc r8, QWORD PTR [rdi+2656]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+2728]
	adc r8, QWORD PTR [rdi+2664]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+2736]
	adc r8, QWORD PTR [rdi+2672]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+2744]
	adc r8, QWORD PTR [rdi+2680]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2688], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+2696], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+2704], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+2712], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+2720], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+2728], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+2736], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+2744], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2688]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2688], rdx
	mov rdx, QWORD PTR [rdi+2696]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2696], rdx
	mov rdx, QWORD PTR [rdi+2704]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2704], rdx
	mov rdx, QWORD PTR [rdi+2712]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2712], rdx
	mov rdx, QWORD PTR [rdi+2720]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2720], rdx
	mov rdx, QWORD PTR [rdi+2728]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2728], rdx
	mov rdx, QWORD PTR [rdi+2736]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2736], rdx
	mov rdx, QWORD PTR [rdi+2744]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2744], rdx
	mov r12, rsi
	mov esi, 2752
	mov edx, 1920
	mov ecx, 2688
	call {vg_brainpoolp512r1_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2816
	mov edx, 2752
	mov ecx, 320
	call {vg_brainpoolp512r1_mul_mod_n}
	mov rsi, r12
	mov rdx, QWORD PTR [rdi+2816]
	or rdx, QWORD PTR [rdi+2824]
	or rdx, QWORD PTR [rdi+2832]
	or rdx, QWORD PTR [rdi+2840]
	or rdx, QWORD PTR [rdi+2848]
	or rdx, QWORD PTR [rdi+2856]
	or rdx, QWORD PTR [rdi+2864]
	or rdx, QWORD PTR [rdi+2872]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2880]
	and rax, rdx
	mov QWORD PTR [rdi+2880], rax
	mov rcx, QWORD PTR [rdi+2880]
	mov rax, QWORD PTR [rdi+2368]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+56], rax
	mov rax, QWORD PTR [rdi+2376]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+48], rax
	mov rax, QWORD PTR [rdi+2384]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+40], rax
	mov rax, QWORD PTR [rdi+2392]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+32], rax
	mov rax, QWORD PTR [rdi+2400]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+24], rax
	mov rax, QWORD PTR [rdi+2408]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rdi+2416]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rdi+2424]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rdi+2816]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+120], rax
	mov rax, QWORD PTR [rdi+2824]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+112], rax
	mov rax, QWORD PTR [rdi+2832]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+104], rax
	mov rax, QWORD PTR [rdi+2840]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+96], rax
	mov rax, QWORD PTR [rdi+2848]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+88], rax
	mov rax, QWORD PTR [rdi+2856]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+80], rax
	mov rax, QWORD PTR [rdi+2864]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+72], rax
	mov rax, QWORD PTR [rdi+2872]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+64], rax
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

vg_ecdsa_brainpoolp512r1_verify:
	mov r8, rcx
	mov r9, rdi
	mov rcx, rdx
	mov r10, rdx
	add r10, 64
	mov rdx, rdi
	add rdx, 1
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r14, rdi
	mov rdi, r8
	mov rax, QWORD PTR [rcx+56]
	bswap rax
	mov QWORD PTR [rdi+2048], rax
	mov rax, QWORD PTR [rcx+48]
	bswap rax
	mov QWORD PTR [rdi+2056], rax
	mov rax, QWORD PTR [rcx+40]
	bswap rax
	mov QWORD PTR [rdi+2064], rax
	mov rax, QWORD PTR [rcx+32]
	bswap rax
	mov QWORD PTR [rdi+2072], rax
	mov rax, QWORD PTR [rcx+24]
	bswap rax
	mov QWORD PTR [rdi+2080], rax
	mov rax, QWORD PTR [rcx+16]
	bswap rax
	mov QWORD PTR [rdi+2088], rax
	mov rax, QWORD PTR [rcx+8]
	bswap rax
	mov QWORD PTR [rdi+2096], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	mov QWORD PTR [rdi+2104], rax
	mov rax, QWORD PTR [rsi+56]
	bswap rax
	mov QWORD PTR [rdi+2112], rax
	mov rax, QWORD PTR [rsi+48]
	bswap rax
	mov QWORD PTR [rdi+2120], rax
	mov rax, QWORD PTR [rsi+40]
	bswap rax
	mov QWORD PTR [rdi+2128], rax
	mov rax, QWORD PTR [rsi+32]
	bswap rax
	mov QWORD PTR [rdi+2136], rax
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rdi+2144], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rdi+2152], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rdi+2160], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rdi+2168], rax
	mov rax, QWORD PTR [rdx+56]
	bswap rax
	mov QWORD PTR [rdi+2176], rax
	mov rax, QWORD PTR [rdx+48]
	bswap rax
	mov QWORD PTR [rdi+2184], rax
	mov rax, QWORD PTR [rdx+40]
	bswap rax
	mov QWORD PTR [rdi+2192], rax
	mov rax, QWORD PTR [rdx+32]
	bswap rax
	mov QWORD PTR [rdi+2200], rax
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+2208], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+2216], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+2224], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+2232], rax
	movabs rax, 2930260431521597683
	mov QWORD PTR [rdi+64], rax
	movabs rax, 2918894611604883077
	mov QWORD PTR [rdi+72], rax
	movabs rax, -5850843135254232858
	mov QWORD PTR [rdi+80], rax
	movabs rax, 9029043254863489090
	mov QWORD PTR [rdi+88], rax
	movabs rax, -2998380533618898831
	mov QWORD PTR [rdi+96], rax
	movabs rax, -3805385882173058546
	mov QWORD PTR [rdi+104], rax
	movabs rax, 4599554755319692295
	mov QWORD PTR [rdi+112], rax
	movabs rax, -6134573700119673717
	mov QWORD PTR [rdi+120], rax
	movabs rax, -5366154943270420375
	mov QWORD PTR [rdi+128], rax
	movabs rax, 2139723849122306781
	mov QWORD PTR [rdi+136], rax
	movabs rax, 4721568021488603207
	mov QWORD PTR [rdi+144], rax
	movabs rax, 6142448377308718617
	mov QWORD PTR [rdi+152], rax
	movabs rax, -2998380533618898832
	mov QWORD PTR [rdi+160], rax
	movabs rax, -3805385882173058546
	mov QWORD PTR [rdi+168], rax
	movabs rax, 4599554755319692295
	mov QWORD PTR [rdi+176], rax
	movabs rax, -6134573700119673717
	mov QWORD PTR [rdi+184], rax
	movabs rax, 0
	mov QWORD PTR [rdi+256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+272], rax
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
	movabs rax, 1
	mov QWORD PTR [rdi+320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+344], rax
	movabs rax, 0
	mov QWORD PTR [rdi+352], rax
	movabs rax, 0
	mov QWORD PTR [rdi+360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+376], rax
	movabs rax, -2930260431521597683
	mov QWORD PTR [rdi+384], rax
	movabs rax, -2918894611604883078
	mov QWORD PTR [rdi+392], rax
	movabs rax, 5850843135254232857
	mov QWORD PTR [rdi+400], rax
	movabs rax, -9029043254863489091
	mov QWORD PTR [rdi+408], rax
	movabs rax, 2998380533618898830
	mov QWORD PTR [rdi+416], rax
	movabs rax, 3805385882173058545
	mov QWORD PTR [rdi+424], rax
	movabs rax, -4599554755319692296
	mov QWORD PTR [rdi+432], rax
	movabs rax, 6134573700119673716
	mov QWORD PTR [rdi+440], rax
	movabs rax, -2729310889293331386
	mov QWORD PTR [rdi+448], rax
	movabs rax, 1505492542499050115
	mov QWORD PTR [rdi+456], rax
	movabs rax, 4661308568508939179
	mov QWORD PTR [rdi+464], rax
	movabs rax, -3490570011004729345
	mov QWORD PTR [rdi+472], rax
	movabs rax, -6490759326330727993
	mov QWORD PTR [rdi+480], rax
	movabs rax, 1742065509884397432
	mov QWORD PTR [rdi+488], rax
	movabs rax, -5171393534022875892
	mov QWORD PTR [rdi+496], rax
	movabs rax, 6828848497702021763
	mov QWORD PTR [rdi+504], rax
	movabs rax, -3976350352470362711
	mov QWORD PTR [rdi+512], rax
	movabs rax, -2787679616831567849
	mov QWORD PTR [rdi+520], rax
	movabs rax, -759617572635022057
	mov QWORD PTR [rdi+528], rax
	movabs rax, -2851632089325841979
	mov QWORD PTR [rdi+536], rax
	movabs rax, -1063825459454450647
	mov QWORD PTR [rdi+544], rax
	movabs rax, -7467397740859902391
	mov QWORD PTR [rdi+552], rax
	movabs rax, -1399404244870167584
	mov QWORD PTR [rdi+560], rax
	movabs rax, -7781545726081636502
	mov QWORD PTR [rdi+568], rax
	movabs rax, -4265306830309041709
	mov QWORD PTR [rdi+576], rax
	movabs rax, 7511526321049830052
	mov QWORD PTR [rdi+584], rax
	movabs rax, 3795131596780428943
	mov QWORD PTR [rdi+592], rax
	movabs rax, -8840474168764915768
	mov QWORD PTR [rdi+600], rax
	movabs rax, 2608665483340973879
	mov QWORD PTR [rdi+608], rax
	movabs rax, -5569006363168916233
	mov QWORD PTR [rdi+616], rax
	movabs rax, -8710887700046199437
	mov QWORD PTR [rdi+624], rax
	movabs rax, 6497464235362412929
	mov QWORD PTR [rdi+632], rax
	movabs rax, 3427351643329669741
	mov QWORD PTR [rdi+640], rax
	movabs rax, 8437739570908558117
	mov QWORD PTR [rdi+648], rax
	movabs rax, -4646495099285039984
	mov QWORD PTR [rdi+656], rax
	movabs rax, 3895270034549689406
	mov QWORD PTR [rdi+664], rax
	movabs rax, 8941628266325094364
	mov QWORD PTR [rdi+672], rax
	movabs rax, 6367293241722486668
	mov QWORD PTR [rdi+680], rax
	movabs rax, -7323178610489081957
	mov QWORD PTR [rdi+688], rax
	movabs rax, -8335941010059464063
	mov QWORD PTR [rdi+696], rax
	movabs rax, -3268654423032195471
	mov QWORD PTR [rdi+704], rax
	movabs rax, 614379990270098909
	mov QWORD PTR [rdi+712], rax
	movabs rax, 4523386233333179007
	mov QWORD PTR [rdi+720], rax
	movabs rax, -6417012887004248088
	mov QWORD PTR [rdi+728], rax
	movabs rax, -2884049621775479325
	mov QWORD PTR [rdi+736], rax
	movabs rax, 8231515388640672735
	mov QWORD PTR [rdi+744], rax
	movabs rax, -7647363628595990954
	mov QWORD PTR [rdi+752], rax
	movabs rax, -6371370358628153424
	mov QWORD PTR [rdi+760], rax
	movabs rax, 5366154943270420375
	mov QWORD PTR [rdi+768], rax
	movabs rax, -2139723849122306782
	mov QWORD PTR [rdi+776], rax
	movabs rax, -4721568021488603208
	mov QWORD PTR [rdi+784], rax
	movabs rax, -6142448377308718618
	mov QWORD PTR [rdi+792], rax
	movabs rax, 2998380533618898831
	mov QWORD PTR [rdi+800], rax
	movabs rax, 3805385882173058545
	mov QWORD PTR [rdi+808], rax
	movabs rax, -4599554755319692296
	mov QWORD PTR [rdi+816], rax
	movabs rax, 6134573700119673716
	mov QWORD PTR [rdi+824], rax
	movabs rax, 2930260431521597681
	mov QWORD PTR [rdi+832], rax
	movabs rax, 2918894611604883077
	mov QWORD PTR [rdi+840], rax
	movabs rax, -5850843135254232858
	mov QWORD PTR [rdi+848], rax
	movabs rax, 9029043254863489090
	mov QWORD PTR [rdi+856], rax
	movabs rax, -2998380533618898831
	mov QWORD PTR [rdi+864], rax
	movabs rax, -3805385882173058546
	mov QWORD PTR [rdi+872], rax
	movabs rax, 4599554755319692295
	mov QWORD PTR [rdi+880], rax
	movabs rax, -6134573700119673717
	mov QWORD PTR [rdi+888], rax
	movabs rax, -5366154943270420377
	mov QWORD PTR [rdi+896], rax
	movabs rax, 2139723849122306781
	mov QWORD PTR [rdi+904], rax
	movabs rax, 4721568021488603207
	mov QWORD PTR [rdi+912], rax
	movabs rax, 6142448377308718617
	mov QWORD PTR [rdi+920], rax
	movabs rax, -2998380533618898832
	mov QWORD PTR [rdi+928], rax
	movabs rax, -3805385882173058546
	mov QWORD PTR [rdi+936], rax
	movabs rax, 4599554755319692295
	mov QWORD PTR [rdi+944], rax
	movabs rax, -6134573700119673717
	mov QWORD PTR [rdi+952], rax
	movabs rax, 0
	mov QWORD PTR [rdi+960], rax
	movabs rax, 0
	mov QWORD PTR [rdi+968], rax
	movabs rax, 0
	mov QWORD PTR [rdi+976], rax
	movabs rax, 0
	mov QWORD PTR [rdi+984], rax
	movabs rax, 0
	mov QWORD PTR [rdi+992], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1000], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1008], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1016], rax
	movabs rax, -2930260431521597683
	mov QWORD PTR [rdi+1024], rax
	movabs rax, -2918894611604883078
	mov QWORD PTR [rdi+1032], rax
	movabs rax, 5850843135254232857
	mov QWORD PTR [rdi+1040], rax
	movabs rax, -9029043254863489091
	mov QWORD PTR [rdi+1048], rax
	movabs rax, 2998380533618898830
	mov QWORD PTR [rdi+1056], rax
	movabs rax, 3805385882173058545
	mov QWORD PTR [rdi+1064], rax
	movabs rax, -4599554755319692296
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 6134573700119673716
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
	movabs rax, 0
	mov QWORD PTR [rdi+1144], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2880], rax
	mov rsi, r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+2048]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2944], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2945], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2946], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2947], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2948], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2949], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2950], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2951], dl
	add rbx, 1
	cmp rbx, 64
	jne 20b
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rdi+rbx*1+832]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3464], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3465], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3466], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3467], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3468], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3469], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3470], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3471], dl
	add rbx, 1
	cmp rbx, 64
	jne 21b
	mov ebx, 0
22:
	movzx eax, BYTE PTR [rdi+rbx*1+896]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3984], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3985], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3986], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3987], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3988], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3989], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3990], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3991], dl
	add rbx, 1
	cmp rbx, 64
	jne 22b
	mov rax, QWORD PTR [r10+56]
	bswap rax
	mov QWORD PTR [rdi+1984], rax
	mov rax, QWORD PTR [r10+48]
	bswap rax
	mov QWORD PTR [rdi+1992], rax
	mov rax, QWORD PTR [r10+40]
	bswap rax
	mov QWORD PTR [rdi+2000], rax
	mov rax, QWORD PTR [r10+32]
	bswap rax
	mov QWORD PTR [rdi+2008], rax
	mov rax, QWORD PTR [r10+24]
	bswap rax
	mov QWORD PTR [rdi+2016], rax
	mov rax, QWORD PTR [r10+16]
	bswap rax
	mov QWORD PTR [rdi+2024], rax
	mov rax, QWORD PTR [r10+8]
	bswap rax
	mov QWORD PTR [rdi+2032], rax
	mov rax, QWORD PTR [r10]
	bswap rax
	mov QWORD PTR [rdi+2040], rax
	movabs rax, 5308921845433037317
	mov QWORD PTR [rdi+2560], rax
	movabs rax, 8736896622494316805
	mov QWORD PTR [rdi+2568], rax
	movabs rax, 6032564814157119443
	mov QWORD PTR [rdi+2576], rax
	movabs rax, -2251348500613608923
	mov QWORD PTR [rdi+2584], rax
	movabs rax, 1821829026357542999
	mov QWORD PTR [rdi+2592], rax
	movabs rax, -6814603332583424125
	mov QWORD PTR [rdi+2600], rax
	movabs rax, 2318818621353553612
	mov QWORD PTR [rdi+2608], rax
	movabs rax, 4345020388158170192
	mov QWORD PTR [rdi+2616], rax
	movabs rax, 5800218050920262196
	mov QWORD PTR [rdi+2624], rax
	movabs rax, 43738331591105076
	mov QWORD PTR [rdi+2632], rax
	movabs rax, -2203486902629751638
	mov QWORD PTR [rdi+2640], rax
	movabs rax, -4089777636057301502
	mov QWORD PTR [rdi+2648], rax
	movabs rax, -7502983355594300365
	mov QWORD PTR [rdi+2656], rax
	movabs rax, -3757594541010986979
	mov QWORD PTR [rdi+2664], rax
	movabs rax, 7215631528053025442
	mov QWORD PTR [rdi+2672], rax
	movabs rax, 7659122907072597671
	mov QWORD PTR [rdi+2680], rax
	mov rdx, r9
	add rdx, 65
	mov rax, QWORD PTR [rdx+56]
	bswap rax
	mov QWORD PTR [rdi+2368], rax
	mov rax, QWORD PTR [rdx+48]
	bswap rax
	mov QWORD PTR [rdi+2376], rax
	mov rax, QWORD PTR [rdx+40]
	bswap rax
	mov QWORD PTR [rdi+2384], rax
	mov rax, QWORD PTR [rdx+32]
	bswap rax
	mov QWORD PTR [rdi+2392], rax
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+2400], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+2408], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+2416], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+2424], rax
	movzx edx, BYTE PTR [r9]
	xor rdx, 4
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2880]
	and rax, rdx
	mov QWORD PTR [rdi+2880], rax
	call {vg_brainpoolp512r1_check_point}
	mov rdx, QWORD PTR [rdi+2048]
	sub rdx, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rdi+2056]
	sbb rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2064]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2072]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2080]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2088]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2096]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2104]
	sbb rdx, QWORD PTR [rdi+184]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+2048]
	or rdx, QWORD PTR [rdi+2056]
	or rdx, QWORD PTR [rdi+2064]
	or rdx, QWORD PTR [rdi+2072]
	or rdx, QWORD PTR [rdi+2080]
	or rdx, QWORD PTR [rdi+2088]
	or rdx, QWORD PTR [rdi+2096]
	or rdx, QWORD PTR [rdi+2104]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+2880]
	and rax, rdx
	mov QWORD PTR [rdi+2880], rax
	mov rdx, QWORD PTR [rdi+1984]
	sub rdx, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rdi+1992]
	sbb rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2000]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2008]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2016]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2024]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2032]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2040]
	sbb rdx, QWORD PTR [rdi+184]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+1984]
	or rdx, QWORD PTR [rdi+1992]
	or rdx, QWORD PTR [rdi+2000]
	or rdx, QWORD PTR [rdi+2008]
	or rdx, QWORD PTR [rdi+2016]
	or rdx, QWORD PTR [rdi+2024]
	or rdx, QWORD PTR [rdi+2032]
	or rdx, QWORD PTR [rdi+2040]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+2880]
	and rax, rdx
	mov QWORD PTR [rdi+2880], rax
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+704]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -5960140139473965017
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+712]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+704]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+136]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -5960140139473965017
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+720]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+712]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+704]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+136]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -5960140139473965017
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+720]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+712]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+704]
	mov rax, QWORD PTR [rdi+2008]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+136]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -5960140139473965017
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+736]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+720]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+712]
	mov rax, QWORD PTR [rdi+2008]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+704]
	mov rax, QWORD PTR [rdi+2016]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+136]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -5960140139473965017
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+744]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+736]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+720]
	mov rax, QWORD PTR [rdi+2008]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+712]
	mov rax, QWORD PTR [rdi+2016]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+704]
	mov rax, QWORD PTR [rdi+2024]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+136]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -5960140139473965017
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+752]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+744]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+736]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+2008]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+720]
	mov rax, QWORD PTR [rdi+2016]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+712]
	mov rax, QWORD PTR [rdi+2024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+704]
	mov rax, QWORD PTR [rdi+2032]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+136]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -5960140139473965017
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+760]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+752]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+744]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+736]
	mov rax, QWORD PTR [rdi+2008]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+2016]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+720]
	mov rax, QWORD PTR [rdi+2024]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+712]
	mov rax, QWORD PTR [rdi+2032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+704]
	mov rax, QWORD PTR [rdi+2040]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+136]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -5960140139473965017
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+760]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+752]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+744]
	mov rax, QWORD PTR [rdi+2008]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+736]
	mov rax, QWORD PTR [rdi+2016]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+2024]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+720]
	mov rax, QWORD PTR [rdi+2032]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+712]
	mov rax, QWORD PTR [rdi+2040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+136]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+760]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+752]
	mov rax, QWORD PTR [rdi+2008]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+744]
	mov rax, QWORD PTR [rdi+2016]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+736]
	mov rax, QWORD PTR [rdi+2024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+2032]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+720]
	mov rax, QWORD PTR [rdi+2040]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+760]
	mov rax, QWORD PTR [rdi+2008]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+752]
	mov rax, QWORD PTR [rdi+2016]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+744]
	mov rax, QWORD PTR [rdi+2024]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+736]
	mov rax, QWORD PTR [rdi+2032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+2040]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+760]
	mov rax, QWORD PTR [rdi+2016]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+752]
	mov rax, QWORD PTR [rdi+2024]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+744]
	mov rax, QWORD PTR [rdi+2032]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+736]
	mov rax, QWORD PTR [rdi+2040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+760]
	mov rax, QWORD PTR [rdi+2024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+752]
	mov rax, QWORD PTR [rdi+2032]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+744]
	mov rax, QWORD PTR [rdi+2040]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+760]
	mov rax, QWORD PTR [rdi+2032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+752]
	mov rax, QWORD PTR [rdi+2040]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+760]
	mov rax, QWORD PTR [rdi+2040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2432], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+2440], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+2448], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+2456], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+2464], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+2472], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+2480], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+2488], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2432]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2432], rdx
	mov rdx, QWORD PTR [rdi+2440]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2440], rdx
	mov rdx, QWORD PTR [rdi+2448]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2448], rdx
	mov rdx, QWORD PTR [rdi+2456]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2456], rdx
	mov rdx, QWORD PTR [rdi+2464]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2464], rdx
	mov rdx, QWORD PTR [rdi+2472]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2472], rdx
	mov rdx, QWORD PTR [rdi+2480]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2480], rdx
	mov rdx, QWORD PTR [rdi+2488]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2488], rdx
	call {vg_brainpoolp512r1_inv_mod_n}
	mov r12, rsi
	mov esi, 2624
	mov edx, 2112
	mov ecx, 704
	call {vg_brainpoolp512r1_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2560
	mov edx, 2048
	mov ecx, 704
	call {vg_brainpoolp512r1_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2688
	mov edx, 2624
	mov ecx, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2752
	mov edx, 2560
	mov ecx, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2240
	mov edx, 2688
	mov ecx, 320
	call {vg_brainpoolp512r1_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2304
	mov edx, 2752
	mov ecx, 320
	call {vg_brainpoolp512r1_mul_mod_n}
	mov rsi, r12
	mov rax, QWORD PTR [rdi+2048]
	mov QWORD PTR [rdi+2112], rax
	mov rax, QWORD PTR [rdi+2056]
	mov QWORD PTR [rdi+2120], rax
	mov rax, QWORD PTR [rdi+2064]
	mov QWORD PTR [rdi+2128], rax
	mov rax, QWORD PTR [rdi+2072]
	mov QWORD PTR [rdi+2136], rax
	mov rax, QWORD PTR [rdi+2080]
	mov QWORD PTR [rdi+2144], rax
	mov rax, QWORD PTR [rdi+2088]
	mov QWORD PTR [rdi+2152], rax
	mov rax, QWORD PTR [rdi+2096]
	mov QWORD PTR [rdi+2160], rax
	mov rax, QWORD PTR [rdi+2104]
	mov QWORD PTR [rdi+2168], rax
	mov rax, QWORD PTR [rdi+2240]
	mov QWORD PTR [rdi+2048], rax
	mov rax, QWORD PTR [rdi+2248]
	mov QWORD PTR [rdi+2056], rax
	mov rax, QWORD PTR [rdi+2256]
	mov QWORD PTR [rdi+2064], rax
	mov rax, QWORD PTR [rdi+2264]
	mov QWORD PTR [rdi+2072], rax
	mov rax, QWORD PTR [rdi+2272]
	mov QWORD PTR [rdi+2080], rax
	mov rax, QWORD PTR [rdi+2280]
	mov QWORD PTR [rdi+2088], rax
	mov rax, QWORD PTR [rdi+2288]
	mov QWORD PTR [rdi+2096], rax
	mov rax, QWORD PTR [rdi+2296]
	mov QWORD PTR [rdi+2104], rax
	mov rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+1016], rax
	mov rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+1024], rax
	mov rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+1032], rax
	mov rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+1040], rax
	mov rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+1048], rax
	mov rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+1080], rax
	call {vg_brainpoolp512r1_mul}
	mov rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+2688], rax
	mov rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+2696], rax
	mov rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+2704], rax
	mov rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+2712], rax
	mov rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+2720], rax
	mov rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+2728], rax
	mov rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+2736], rax
	mov rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+2744], rax
	mov rax, QWORD PTR [rdi+1024]
	mov QWORD PTR [rdi+2752], rax
	mov rax, QWORD PTR [rdi+1032]
	mov QWORD PTR [rdi+2760], rax
	mov rax, QWORD PTR [rdi+1040]
	mov QWORD PTR [rdi+2768], rax
	mov rax, QWORD PTR [rdi+1048]
	mov QWORD PTR [rdi+2776], rax
	mov rax, QWORD PTR [rdi+1056]
	mov QWORD PTR [rdi+2784], rax
	mov rax, QWORD PTR [rdi+1064]
	mov QWORD PTR [rdi+2792], rax
	mov rax, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+2800], rax
	mov rax, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+2808], rax
	mov rax, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+2432], rax
	mov rax, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+2440], rax
	mov rax, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+2448], rax
	mov rax, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+2456], rax
	mov rax, QWORD PTR [rdi+1120]
	mov QWORD PTR [rdi+2464], rax
	mov rax, QWORD PTR [rdi+1128]
	mov QWORD PTR [rdi+2472], rax
	mov rax, QWORD PTR [rdi+1136]
	mov QWORD PTR [rdi+2480], rax
	mov rax, QWORD PTR [rdi+1144]
	mov QWORD PTR [rdi+2488], rax
	movabs rax, 0
	mov QWORD PTR [rdi+960], rax
	movabs rax, 0
	mov QWORD PTR [rdi+968], rax
	movabs rax, 0
	mov QWORD PTR [rdi+976], rax
	movabs rax, 0
	mov QWORD PTR [rdi+984], rax
	movabs rax, 0
	mov QWORD PTR [rdi+992], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1000], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1008], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1016], rax
	movabs rax, -2930260431521597683
	mov QWORD PTR [rdi+1024], rax
	movabs rax, -2918894611604883078
	mov QWORD PTR [rdi+1032], rax
	movabs rax, 5850843135254232857
	mov QWORD PTR [rdi+1040], rax
	movabs rax, -9029043254863489091
	mov QWORD PTR [rdi+1048], rax
	movabs rax, 2998380533618898830
	mov QWORD PTR [rdi+1056], rax
	movabs rax, 3805385882173058545
	mov QWORD PTR [rdi+1064], rax
	movabs rax, -4599554755319692296
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 6134573700119673716
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
	movabs rax, 0
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+2304]
	mov QWORD PTR [rdi+2048], rax
	mov rax, QWORD PTR [rdi+2312]
	mov QWORD PTR [rdi+2056], rax
	mov rax, QWORD PTR [rdi+2320]
	mov QWORD PTR [rdi+2064], rax
	mov rax, QWORD PTR [rdi+2328]
	mov QWORD PTR [rdi+2072], rax
	mov rax, QWORD PTR [rdi+2336]
	mov QWORD PTR [rdi+2080], rax
	mov rax, QWORD PTR [rdi+2344]
	mov QWORD PTR [rdi+2088], rax
	mov rax, QWORD PTR [rdi+2352]
	mov QWORD PTR [rdi+2096], rax
	mov rax, QWORD PTR [rdi+2360]
	mov QWORD PTR [rdi+2104], rax
	mov rax, QWORD PTR [rdi+2496]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rdi+2504]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rdi+2512]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rdi+2520]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rdi+2528]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rdi+2536]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rdi+2544]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rdi+2552]
	mov QWORD PTR [rdi+1016], rax
	mov rax, QWORD PTR [rdi+2816]
	mov QWORD PTR [rdi+1024], rax
	mov rax, QWORD PTR [rdi+2824]
	mov QWORD PTR [rdi+1032], rax
	mov rax, QWORD PTR [rdi+2832]
	mov QWORD PTR [rdi+1040], rax
	mov rax, QWORD PTR [rdi+2840]
	mov QWORD PTR [rdi+1048], rax
	mov rax, QWORD PTR [rdi+2848]
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rdi+2856]
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rdi+2864]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+2872]
	mov QWORD PTR [rdi+1080], rax
	call {vg_brainpoolp512r1_mul}
	mov r12, rsi
	mov esi, 1536
	mov edx, 2688
	mov ecx, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1600
	mov edx, 2752
	mov ecx, 1024
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1664
	mov edx, 2432
	mov ecx, 1088
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r9d, 0
	mov r8, QWORD PTR [rdi+2688]
	add r8, QWORD PTR [rdi+2752]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+2696]
	adc r8, QWORD PTR [rdi+2760]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+2704]
	adc r8, QWORD PTR [rdi+2768]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+2712]
	adc r8, QWORD PTR [rdi+2776]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+2720]
	adc r8, QWORD PTR [rdi+2784]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+2728]
	adc r8, QWORD PTR [rdi+2792]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+2736]
	adc r8, QWORD PTR [rdi+2800]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+2744]
	adc r8, QWORD PTR [rdi+2808]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1728], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1736], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1744], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1752], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1760], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1768], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1776], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1784], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1728]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1728], rdx
	mov rdx, QWORD PTR [rdi+1736]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1736], rdx
	mov rdx, QWORD PTR [rdi+1744]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1744], rdx
	mov rdx, QWORD PTR [rdi+1752]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1752], rdx
	mov rdx, QWORD PTR [rdi+1760]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1760], rdx
	mov rdx, QWORD PTR [rdi+1768]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1768], rdx
	mov rdx, QWORD PTR [rdi+1776]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1776], rdx
	mov rdx, QWORD PTR [rdi+1784]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1784], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+960]
	add r8, QWORD PTR [rdi+1024]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+968]
	adc r8, QWORD PTR [rdi+1032]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+976]
	adc r8, QWORD PTR [rdi+1040]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+984]
	adc r8, QWORD PTR [rdi+1048]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+992]
	adc r8, QWORD PTR [rdi+1056]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1000]
	adc r8, QWORD PTR [rdi+1064]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1008]
	adc r8, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1016]
	adc r8, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov r12, rsi
	mov esi, 1728
	mov edx, 1728
	mov ecx, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1536]
	add r8, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1544]
	adc r8, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1552]
	adc r8, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1560]
	adc r8, QWORD PTR [rdi+1624]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1568]
	adc r8, QWORD PTR [rdi+1632]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1576]
	adc r8, QWORD PTR [rdi+1640]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1584]
	adc r8, QWORD PTR [rdi+1648]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1592]
	adc r8, QWORD PTR [rdi+1656]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov r8, QWORD PTR [rdi+1728]
	sub r8, QWORD PTR [rdi+1792]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1736]
	sbb r8, QWORD PTR [rdi+1800]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1744]
	sbb r8, QWORD PTR [rdi+1808]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1752]
	sbb r8, QWORD PTR [rdi+1816]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1760]
	sbb r8, QWORD PTR [rdi+1824]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1768]
	sbb r8, QWORD PTR [rdi+1832]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1776]
	sbb r8, QWORD PTR [rdi+1840]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1784]
	sbb r8, QWORD PTR [rdi+1848]
	mov QWORD PTR [rdi+4088], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1728], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1736], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1744], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1752], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1760], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1768], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1776], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1784], rdx
	mov r8, QWORD PTR [rdi+4032]
	add r8, QWORD PTR [rdi+1728]
	mov QWORD PTR [rdi+1728], r8
	mov r8, QWORD PTR [rdi+4040]
	adc r8, QWORD PTR [rdi+1736]
	mov QWORD PTR [rdi+1736], r8
	mov r8, QWORD PTR [rdi+4048]
	adc r8, QWORD PTR [rdi+1744]
	mov QWORD PTR [rdi+1744], r8
	mov r8, QWORD PTR [rdi+4056]
	adc r8, QWORD PTR [rdi+1752]
	mov QWORD PTR [rdi+1752], r8
	mov r8, QWORD PTR [rdi+4064]
	adc r8, QWORD PTR [rdi+1760]
	mov QWORD PTR [rdi+1760], r8
	mov r8, QWORD PTR [rdi+4072]
	adc r8, QWORD PTR [rdi+1768]
	mov QWORD PTR [rdi+1768], r8
	mov r8, QWORD PTR [rdi+4080]
	adc r8, QWORD PTR [rdi+1776]
	mov QWORD PTR [rdi+1776], r8
	mov r8, QWORD PTR [rdi+4088]
	adc r8, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+1784], r8
	mov r9d, 0
	mov r8, QWORD PTR [rdi+2688]
	add r8, QWORD PTR [rdi+2432]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+2696]
	adc r8, QWORD PTR [rdi+2440]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+2704]
	adc r8, QWORD PTR [rdi+2448]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+2712]
	adc r8, QWORD PTR [rdi+2456]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+2720]
	adc r8, QWORD PTR [rdi+2464]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+2728]
	adc r8, QWORD PTR [rdi+2472]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+2736]
	adc r8, QWORD PTR [rdi+2480]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+2744]
	adc r8, QWORD PTR [rdi+2488]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+960]
	add r8, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+968]
	adc r8, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+976]
	adc r8, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+984]
	adc r8, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+992]
	adc r8, QWORD PTR [rdi+1120]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1000]
	adc r8, QWORD PTR [rdi+1128]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1008]
	adc r8, QWORD PTR [rdi+1136]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1016]
	adc r8, QWORD PTR [rdi+1144]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1856], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1864], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1872], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1880], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1888], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1896], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1904], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1912], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1856]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1856], rdx
	mov rdx, QWORD PTR [rdi+1864]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1864], rdx
	mov rdx, QWORD PTR [rdi+1872]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1872], rdx
	mov rdx, QWORD PTR [rdi+1880]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1880], rdx
	mov rdx, QWORD PTR [rdi+1888]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1888], rdx
	mov rdx, QWORD PTR [rdi+1896]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1896], rdx
	mov rdx, QWORD PTR [rdi+1904]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1904], rdx
	mov rdx, QWORD PTR [rdi+1912]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1912], rdx
	mov r12, rsi
	mov esi, 1792
	mov edx, 1792
	mov ecx, 1856
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1536]
	add r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1544]
	adc r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1552]
	adc r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1560]
	adc r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1568]
	adc r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1576]
	adc r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1584]
	adc r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1592]
	adc r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1856], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1864], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1872], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1880], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1888], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1896], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1904], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1912], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1856]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1856], rdx
	mov rdx, QWORD PTR [rdi+1864]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1864], rdx
	mov rdx, QWORD PTR [rdi+1872]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1872], rdx
	mov rdx, QWORD PTR [rdi+1880]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1880], rdx
	mov rdx, QWORD PTR [rdi+1888]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1888], rdx
	mov rdx, QWORD PTR [rdi+1896]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1896], rdx
	mov rdx, QWORD PTR [rdi+1904]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1904], rdx
	mov rdx, QWORD PTR [rdi+1912]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1912], rdx
	mov r8, QWORD PTR [rdi+1792]
	sub r8, QWORD PTR [rdi+1856]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1800]
	sbb r8, QWORD PTR [rdi+1864]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1808]
	sbb r8, QWORD PTR [rdi+1872]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1816]
	sbb r8, QWORD PTR [rdi+1880]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1824]
	sbb r8, QWORD PTR [rdi+1888]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1832]
	sbb r8, QWORD PTR [rdi+1896]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1840]
	sbb r8, QWORD PTR [rdi+1904]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1848]
	sbb r8, QWORD PTR [rdi+1912]
	mov QWORD PTR [rdi+4088], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1848], rdx
	mov r8, QWORD PTR [rdi+4032]
	add r8, QWORD PTR [rdi+1792]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+4040]
	adc r8, QWORD PTR [rdi+1800]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+4048]
	adc r8, QWORD PTR [rdi+1808]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+4056]
	adc r8, QWORD PTR [rdi+1816]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+4064]
	adc r8, QWORD PTR [rdi+1824]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+4072]
	adc r8, QWORD PTR [rdi+1832]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+4080]
	adc r8, QWORD PTR [rdi+1840]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+4088]
	adc r8, QWORD PTR [rdi+1848]
	mov QWORD PTR [rdi+1848], r8
	mov r9d, 0
	mov r8, QWORD PTR [rdi+2752]
	add r8, QWORD PTR [rdi+2432]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+2760]
	adc r8, QWORD PTR [rdi+2440]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+2768]
	adc r8, QWORD PTR [rdi+2448]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+2776]
	adc r8, QWORD PTR [rdi+2456]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+2784]
	adc r8, QWORD PTR [rdi+2464]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+2792]
	adc r8, QWORD PTR [rdi+2472]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+2800]
	adc r8, QWORD PTR [rdi+2480]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+2808]
	adc r8, QWORD PTR [rdi+2488]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1856], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1864], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1872], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1880], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1888], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1896], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1904], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1912], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1856]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1856], rdx
	mov rdx, QWORD PTR [rdi+1864]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1864], rdx
	mov rdx, QWORD PTR [rdi+1872]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1872], rdx
	mov rdx, QWORD PTR [rdi+1880]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1880], rdx
	mov rdx, QWORD PTR [rdi+1888]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1888], rdx
	mov rdx, QWORD PTR [rdi+1896]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1896], rdx
	mov rdx, QWORD PTR [rdi+1904]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1904], rdx
	mov rdx, QWORD PTR [rdi+1912]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1912], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1024]
	add r8, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1032]
	adc r8, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1040]
	adc r8, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1048]
	adc r8, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1056]
	adc r8, QWORD PTR [rdi+1120]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1064]
	adc r8, QWORD PTR [rdi+1128]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1072]
	adc r8, QWORD PTR [rdi+1136]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1080]
	adc r8, QWORD PTR [rdi+1144]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1152], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1160], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1168], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1176], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1184], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1192], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1200], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1208], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1152]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1152], rdx
	mov rdx, QWORD PTR [rdi+1160]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1160], rdx
	mov rdx, QWORD PTR [rdi+1168]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1168], rdx
	mov rdx, QWORD PTR [rdi+1176]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1176], rdx
	mov rdx, QWORD PTR [rdi+1184]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1184], rdx
	mov rdx, QWORD PTR [rdi+1192]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1192], rdx
	mov rdx, QWORD PTR [rdi+1200]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1200], rdx
	mov rdx, QWORD PTR [rdi+1208]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1208], rdx
	mov r12, rsi
	mov esi, 1856
	mov edx, 1856
	mov ecx, 1152
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1600]
	add r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1608]
	adc r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1616]
	adc r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1624]
	adc r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1632]
	adc r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1640]
	adc r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1648]
	adc r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1656]
	adc r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1152], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1160], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1168], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1176], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1184], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1192], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1200], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1208], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1152]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1152], rdx
	mov rdx, QWORD PTR [rdi+1160]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1160], rdx
	mov rdx, QWORD PTR [rdi+1168]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1168], rdx
	mov rdx, QWORD PTR [rdi+1176]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1176], rdx
	mov rdx, QWORD PTR [rdi+1184]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1184], rdx
	mov rdx, QWORD PTR [rdi+1192]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1192], rdx
	mov rdx, QWORD PTR [rdi+1200]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1200], rdx
	mov rdx, QWORD PTR [rdi+1208]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1208], rdx
	mov r8, QWORD PTR [rdi+1856]
	sub r8, QWORD PTR [rdi+1152]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1864]
	sbb r8, QWORD PTR [rdi+1160]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1872]
	sbb r8, QWORD PTR [rdi+1168]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1880]
	sbb r8, QWORD PTR [rdi+1176]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1888]
	sbb r8, QWORD PTR [rdi+1184]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1896]
	sbb r8, QWORD PTR [rdi+1192]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1904]
	sbb r8, QWORD PTR [rdi+1200]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1912]
	sbb r8, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+4088], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1856], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1864], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1872], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1880], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1888], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1896], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1904], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1912], rdx
	mov r8, QWORD PTR [rdi+4032]
	add r8, QWORD PTR [rdi+1856]
	mov QWORD PTR [rdi+1856], r8
	mov r8, QWORD PTR [rdi+4040]
	adc r8, QWORD PTR [rdi+1864]
	mov QWORD PTR [rdi+1864], r8
	mov r8, QWORD PTR [rdi+4048]
	adc r8, QWORD PTR [rdi+1872]
	mov QWORD PTR [rdi+1872], r8
	mov r8, QWORD PTR [rdi+4056]
	adc r8, QWORD PTR [rdi+1880]
	mov QWORD PTR [rdi+1880], r8
	mov r8, QWORD PTR [rdi+4064]
	adc r8, QWORD PTR [rdi+1888]
	mov QWORD PTR [rdi+1888], r8
	mov r8, QWORD PTR [rdi+4072]
	adc r8, QWORD PTR [rdi+1896]
	mov QWORD PTR [rdi+1896], r8
	mov r8, QWORD PTR [rdi+4080]
	adc r8, QWORD PTR [rdi+1904]
	mov QWORD PTR [rdi+1904], r8
	mov r8, QWORD PTR [rdi+4088]
	adc r8, QWORD PTR [rdi+1912]
	mov QWORD PTR [rdi+1912], r8
	mov r12, rsi
	mov esi, 1280
	mov edx, 448
	mov ecx, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1152
	mov edx, 512
	mov ecx, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1152]
	add r8, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1160]
	adc r8, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1168]
	adc r8, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1176]
	adc r8, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1184]
	adc r8, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1192]
	adc r8, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1200]
	adc r8, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1208]
	adc r8, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1280], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1288], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1296], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1304], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1312], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1320], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1328], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1336], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1280]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1280], rdx
	mov rdx, QWORD PTR [rdi+1288]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1288], rdx
	mov rdx, QWORD PTR [rdi+1296]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1296], rdx
	mov rdx, QWORD PTR [rdi+1304]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1304], rdx
	mov rdx, QWORD PTR [rdi+1312]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1312], rdx
	mov rdx, QWORD PTR [rdi+1320]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1320], rdx
	mov rdx, QWORD PTR [rdi+1328]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1328], rdx
	mov rdx, QWORD PTR [rdi+1336]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1336], rdx
	mov r8, QWORD PTR [rdi+1600]
	sub r8, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1608]
	sbb r8, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1616]
	sbb r8, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1624]
	sbb r8, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1632]
	sbb r8, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1640]
	sbb r8, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1648]
	sbb r8, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1656]
	sbb r8, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+4088], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1152], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1160], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1168], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1176], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1184], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1192], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1200], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1208], rdx
	mov r8, QWORD PTR [rdi+4032]
	add r8, QWORD PTR [rdi+1152]
	mov QWORD PTR [rdi+1152], r8
	mov r8, QWORD PTR [rdi+4040]
	adc r8, QWORD PTR [rdi+1160]
	mov QWORD PTR [rdi+1160], r8
	mov r8, QWORD PTR [rdi+4048]
	adc r8, QWORD PTR [rdi+1168]
	mov QWORD PTR [rdi+1168], r8
	mov r8, QWORD PTR [rdi+4056]
	adc r8, QWORD PTR [rdi+1176]
	mov QWORD PTR [rdi+1176], r8
	mov r8, QWORD PTR [rdi+4064]
	adc r8, QWORD PTR [rdi+1184]
	mov QWORD PTR [rdi+1184], r8
	mov r8, QWORD PTR [rdi+4072]
	adc r8, QWORD PTR [rdi+1192]
	mov QWORD PTR [rdi+1192], r8
	mov r8, QWORD PTR [rdi+4080]
	adc r8, QWORD PTR [rdi+1200]
	mov QWORD PTR [rdi+1200], r8
	mov r8, QWORD PTR [rdi+4088]
	adc r8, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+1208], r8
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1600]
	add r8, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1608]
	adc r8, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1616]
	adc r8, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1624]
	adc r8, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1632]
	adc r8, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1640]
	adc r8, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1648]
	adc r8, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1656]
	adc r8, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1280], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1288], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1296], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1304], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1312], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1320], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1328], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1336], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1280]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1280], rdx
	mov rdx, QWORD PTR [rdi+1288]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1288], rdx
	mov rdx, QWORD PTR [rdi+1296]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1296], rdx
	mov rdx, QWORD PTR [rdi+1304]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1304], rdx
	mov rdx, QWORD PTR [rdi+1312]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1312], rdx
	mov rdx, QWORD PTR [rdi+1320]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1320], rdx
	mov rdx, QWORD PTR [rdi+1328]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1328], rdx
	mov rdx, QWORD PTR [rdi+1336]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1336], rdx
	mov r12, rsi
	mov esi, 1216
	mov edx, 1152
	mov ecx, 1280
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1536]
	add r8, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1544]
	adc r8, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1552]
	adc r8, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1560]
	adc r8, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1568]
	adc r8, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1576]
	adc r8, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1584]
	adc r8, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1592]
	adc r8, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1600], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1608], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1616], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1624], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1632], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1640], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1648], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1656], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1600]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1600], rdx
	mov rdx, QWORD PTR [rdi+1608]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1608], rdx
	mov rdx, QWORD PTR [rdi+1616]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1616], rdx
	mov rdx, QWORD PTR [rdi+1624]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1624], rdx
	mov rdx, QWORD PTR [rdi+1632]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1632], rdx
	mov rdx, QWORD PTR [rdi+1640]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1640], rdx
	mov rdx, QWORD PTR [rdi+1648]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1648], rdx
	mov rdx, QWORD PTR [rdi+1656]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1656], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1600]
	add r8, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1608]
	adc r8, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1616]
	adc r8, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1624]
	adc r8, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1632]
	adc r8, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1640]
	adc r8, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1648]
	adc r8, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1656]
	adc r8, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1600], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1608], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1616], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1624], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1632], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1640], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1648], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1656], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1600]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1600], rdx
	mov rdx, QWORD PTR [rdi+1608]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1608], rdx
	mov rdx, QWORD PTR [rdi+1616]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1616], rdx
	mov rdx, QWORD PTR [rdi+1624]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1624], rdx
	mov rdx, QWORD PTR [rdi+1632]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1632], rdx
	mov rdx, QWORD PTR [rdi+1640]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1640], rdx
	mov rdx, QWORD PTR [rdi+1648]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1648], rdx
	mov rdx, QWORD PTR [rdi+1656]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1656], rdx
	mov r12, rsi
	mov esi, 1664
	mov edx, 448
	mov ecx, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 512
	mov ecx, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1600]
	add r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1608]
	adc r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1616]
	adc r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1624]
	adc r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1632]
	adc r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1640]
	adc r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1648]
	adc r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1656]
	adc r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1600], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1608], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1616], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1624], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1632], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1640], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1648], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1656], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1600]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1600], rdx
	mov rdx, QWORD PTR [rdi+1608]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1608], rdx
	mov rdx, QWORD PTR [rdi+1616]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1616], rdx
	mov rdx, QWORD PTR [rdi+1624]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1624], rdx
	mov rdx, QWORD PTR [rdi+1632]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1632], rdx
	mov rdx, QWORD PTR [rdi+1640]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1640], rdx
	mov rdx, QWORD PTR [rdi+1648]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1648], rdx
	mov rdx, QWORD PTR [rdi+1656]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1656], rdx
	mov r8, QWORD PTR [rdi+1536]
	sub r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1544]
	sbb r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1552]
	sbb r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1560]
	sbb r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1568]
	sbb r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1576]
	sbb r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1584]
	sbb r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1592]
	sbb r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+4088], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1664], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1672], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1680], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1688], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1696], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1704], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1712], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1720], rdx
	mov r8, QWORD PTR [rdi+4032]
	add r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+1664], r8
	mov r8, QWORD PTR [rdi+4040]
	adc r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+1672], r8
	mov r8, QWORD PTR [rdi+4048]
	adc r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+1680], r8
	mov r8, QWORD PTR [rdi+4056]
	adc r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+1688], r8
	mov r8, QWORD PTR [rdi+4064]
	adc r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+1696], r8
	mov r8, QWORD PTR [rdi+4072]
	adc r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+1704], r8
	mov r8, QWORD PTR [rdi+4080]
	adc r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+1712], r8
	mov r8, QWORD PTR [rdi+4088]
	adc r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+1720], r8
	mov r12, rsi
	mov esi, 1664
	mov edx, 448
	mov ecx, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1792]
	add r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1800]
	adc r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1808]
	adc r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1816]
	adc r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1824]
	adc r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1832]
	adc r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1840]
	adc r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1848]
	adc r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov r12, rsi
	mov esi, 1536
	mov edx, 1600
	mov ecx, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1216]
	add r8, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1224]
	adc r8, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1232]
	adc r8, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1240]
	adc r8, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1248]
	adc r8, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1256]
	adc r8, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1264]
	adc r8, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1272]
	adc r8, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1216], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1224], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1232], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1240], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1248], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1256], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1264], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1272], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1216]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1216], rdx
	mov rdx, QWORD PTR [rdi+1224]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1224], rdx
	mov rdx, QWORD PTR [rdi+1232]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1232], rdx
	mov rdx, QWORD PTR [rdi+1240]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1240], rdx
	mov rdx, QWORD PTR [rdi+1248]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1248], rdx
	mov rdx, QWORD PTR [rdi+1256]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1256], rdx
	mov rdx, QWORD PTR [rdi+1264]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1264], rdx
	mov rdx, QWORD PTR [rdi+1272]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1272], rdx
	mov r12, rsi
	mov esi, 1536
	mov edx, 1856
	mov ecx, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1152
	mov edx, 1728
	mov ecx, 1152
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r8, QWORD PTR [rdi+1152]
	sub r8, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1160]
	sbb r8, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1168]
	sbb r8, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1176]
	sbb r8, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1184]
	sbb r8, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1192]
	sbb r8, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1200]
	sbb r8, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1208]
	sbb r8, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+4088], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1152], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1160], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1168], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1176], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1184], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1192], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1200], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1208], rdx
	mov r8, QWORD PTR [rdi+4032]
	add r8, QWORD PTR [rdi+1152]
	mov QWORD PTR [rdi+1152], r8
	mov r8, QWORD PTR [rdi+4040]
	adc r8, QWORD PTR [rdi+1160]
	mov QWORD PTR [rdi+1160], r8
	mov r8, QWORD PTR [rdi+4048]
	adc r8, QWORD PTR [rdi+1168]
	mov QWORD PTR [rdi+1168], r8
	mov r8, QWORD PTR [rdi+4056]
	adc r8, QWORD PTR [rdi+1176]
	mov QWORD PTR [rdi+1176], r8
	mov r8, QWORD PTR [rdi+4064]
	adc r8, QWORD PTR [rdi+1184]
	mov QWORD PTR [rdi+1184], r8
	mov r8, QWORD PTR [rdi+4072]
	adc r8, QWORD PTR [rdi+1192]
	mov QWORD PTR [rdi+1192], r8
	mov r8, QWORD PTR [rdi+4080]
	adc r8, QWORD PTR [rdi+1200]
	mov QWORD PTR [rdi+1200], r8
	mov r8, QWORD PTR [rdi+4088]
	adc r8, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+1208], r8
	mov r12, rsi
	mov esi, 1536
	mov edx, 1728
	mov ecx, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1280
	mov edx, 1856
	mov ecx, 1280
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1280]
	add r8, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+1288]
	adc r8, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+1296]
	adc r8, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+1304]
	adc r8, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+1312]
	adc r8, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+1320]
	adc r8, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+1328]
	adc r8, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+1336]
	adc r8, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4032]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1280], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1288], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1296], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1304], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1312], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1320], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1328], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1336], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1280]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1280], rdx
	mov rdx, QWORD PTR [rdi+1288]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1288], rdx
	mov rdx, QWORD PTR [rdi+1296]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1296], rdx
	mov rdx, QWORD PTR [rdi+1304]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1304], rdx
	mov rdx, QWORD PTR [rdi+1312]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1312], rdx
	mov rdx, QWORD PTR [rdi+1320]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1320], rdx
	mov rdx, QWORD PTR [rdi+1328]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1328], rdx
	mov rdx, QWORD PTR [rdi+1336]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1336], rdx
	mov rax, QWORD PTR [rdi+1152]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rdi+1160]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rdi+1168]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rdi+1176]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rdi+1184]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rdi+1192]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rdi+1200]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+1016], rax
	mov rax, QWORD PTR [rdi+1216]
	mov QWORD PTR [rdi+1024], rax
	mov rax, QWORD PTR [rdi+1224]
	mov QWORD PTR [rdi+1032], rax
	mov rax, QWORD PTR [rdi+1232]
	mov QWORD PTR [rdi+1040], rax
	mov rax, QWORD PTR [rdi+1240]
	mov QWORD PTR [rdi+1048], rax
	mov rax, QWORD PTR [rdi+1248]
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rdi+1256]
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rdi+1264]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1272]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+2112]
	mov QWORD PTR [rdi+2048], rax
	mov rax, QWORD PTR [rdi+2120]
	mov QWORD PTR [rdi+2056], rax
	mov rax, QWORD PTR [rdi+2128]
	mov QWORD PTR [rdi+2064], rax
	mov rax, QWORD PTR [rdi+2136]
	mov QWORD PTR [rdi+2072], rax
	mov rax, QWORD PTR [rdi+2144]
	mov QWORD PTR [rdi+2080], rax
	mov rax, QWORD PTR [rdi+2152]
	mov QWORD PTR [rdi+2088], rax
	mov rax, QWORD PTR [rdi+2160]
	mov QWORD PTR [rdi+2096], rax
	mov rax, QWORD PTR [rdi+2168]
	mov QWORD PTR [rdi+2104], rax
	call {vg_brainpoolp512r1_inv_mod_p}
	mov r12, rsi
	mov esi, 2240
	mov edx, 960
	mov ecx, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2304
	mov edx, 2240
	mov ecx, 320
	call {vg_brainpoolp512r1_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2496
	mov edx, 2304
	mov ecx, 704
	call {vg_brainpoolp512r1_mul_mod_n}
	mov rsi, r12
	mov r8, QWORD PTR [rdi+2496]
	sub r8, QWORD PTR [rdi+2560]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+2504]
	sbb r8, QWORD PTR [rdi+2568]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+2512]
	sbb r8, QWORD PTR [rdi+2576]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+2520]
	sbb r8, QWORD PTR [rdi+2584]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+2528]
	sbb r8, QWORD PTR [rdi+2592]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+2536]
	sbb r8, QWORD PTR [rdi+2600]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+2544]
	sbb r8, QWORD PTR [rdi+2608]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+2552]
	sbb r8, QWORD PTR [rdi+2616]
	mov QWORD PTR [rdi+248], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+128]
	and rdx, rax
	mov QWORD PTR [rdi+2624], rdx
	mov rdx, QWORD PTR [rdi+136]
	and rdx, rax
	mov QWORD PTR [rdi+2632], rdx
	mov rdx, QWORD PTR [rdi+144]
	and rdx, rax
	mov QWORD PTR [rdi+2640], rdx
	mov rdx, QWORD PTR [rdi+152]
	and rdx, rax
	mov QWORD PTR [rdi+2648], rdx
	mov rdx, QWORD PTR [rdi+160]
	and rdx, rax
	mov QWORD PTR [rdi+2656], rdx
	mov rdx, QWORD PTR [rdi+168]
	and rdx, rax
	mov QWORD PTR [rdi+2664], rdx
	mov rdx, QWORD PTR [rdi+176]
	and rdx, rax
	mov QWORD PTR [rdi+2672], rdx
	mov rdx, QWORD PTR [rdi+184]
	and rdx, rax
	mov QWORD PTR [rdi+2680], rdx
	mov r8, QWORD PTR [rdi+192]
	add r8, QWORD PTR [rdi+2624]
	mov QWORD PTR [rdi+2624], r8
	mov r8, QWORD PTR [rdi+200]
	adc r8, QWORD PTR [rdi+2632]
	mov QWORD PTR [rdi+2632], r8
	mov r8, QWORD PTR [rdi+208]
	adc r8, QWORD PTR [rdi+2640]
	mov QWORD PTR [rdi+2640], r8
	mov r8, QWORD PTR [rdi+216]
	adc r8, QWORD PTR [rdi+2648]
	mov QWORD PTR [rdi+2648], r8
	mov r8, QWORD PTR [rdi+224]
	adc r8, QWORD PTR [rdi+2656]
	mov QWORD PTR [rdi+2656], r8
	mov r8, QWORD PTR [rdi+232]
	adc r8, QWORD PTR [rdi+2664]
	mov QWORD PTR [rdi+2664], r8
	mov r8, QWORD PTR [rdi+240]
	adc r8, QWORD PTR [rdi+2672]
	mov QWORD PTR [rdi+2672], r8
	mov r8, QWORD PTR [rdi+248]
	adc r8, QWORD PTR [rdi+2680]
	mov QWORD PTR [rdi+2680], r8
	mov rdx, QWORD PTR [rdi+1088]
	or rdx, QWORD PTR [rdi+1096]
	or rdx, QWORD PTR [rdi+1104]
	or rdx, QWORD PTR [rdi+1112]
	or rdx, QWORD PTR [rdi+1120]
	or rdx, QWORD PTR [rdi+1128]
	or rdx, QWORD PTR [rdi+1136]
	or rdx, QWORD PTR [rdi+1144]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2880]
	and rax, rdx
	mov QWORD PTR [rdi+2880], rax
	mov rdx, QWORD PTR [rdi+2624]
	or rdx, QWORD PTR [rdi+2632]
	or rdx, QWORD PTR [rdi+2640]
	or rdx, QWORD PTR [rdi+2648]
	or rdx, QWORD PTR [rdi+2656]
	or rdx, QWORD PTR [rdi+2664]
	or rdx, QWORD PTR [rdi+2672]
	or rdx, QWORD PTR [rdi+2680]
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2880]
	and rax, rdx
	mov QWORD PTR [rdi+2880], rax
	mov rax, QWORD PTR [rdi+2880]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6
