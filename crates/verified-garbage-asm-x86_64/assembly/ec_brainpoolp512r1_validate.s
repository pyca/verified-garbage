// The functions of `src/ec_brainpoolp512r1_validate.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp512r1_validate_public_key:
	mov r8, rsi
	mov r9, rdi
	mov rcx, rdi
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
	mov rcx, QWORD PTR [rdi+2880]
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
