// The functions of `src/ecdsa_brainpoolp384r1.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp384r1_verify:
	mov r8, rcx
	mov r9, rdi
	mov rcx, rdx
	mov r10, rdx
	add r10, 48
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
	mov rax, QWORD PTR [rcx+40]
	bswap rax
	mov QWORD PTR [rdi+1552], rax
	mov rax, QWORD PTR [rcx+32]
	bswap rax
	mov QWORD PTR [rdi+1560], rax
	mov rax, QWORD PTR [rcx+24]
	bswap rax
	mov QWORD PTR [rdi+1568], rax
	mov rax, QWORD PTR [rcx+16]
	bswap rax
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rcx+8]
	bswap rax
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rsi+40]
	bswap rax
	mov QWORD PTR [rdi+1600], rax
	mov rax, QWORD PTR [rsi+32]
	bswap rax
	mov QWORD PTR [rdi+1608], rax
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rdi+1616], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rdi+1624], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rdi+1632], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rdi+1640], rax
	mov rax, QWORD PTR [rdx+40]
	bswap rax
	mov QWORD PTR [rdi+1648], rax
	mov rax, QWORD PTR [rdx+32]
	bswap rax
	mov QWORD PTR [rdi+1656], rax
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1664], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1672], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1680], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1688], rax
	movabs rax, -8698984072815842221
	mov QWORD PTR [rdi+64], rax
	movabs rax, -5993262882146674063
	mov QWORD PTR [rdi+72], rax
	movabs rax, 1347097566612230435
	mov QWORD PTR [rdi+80], rax
	movabs rax, 1526563086152259252
	mov QWORD PTR [rdi+88], rax
	movabs rax, 1107163671716839903
	mov QWORD PTR [rdi+96], rax
	movabs rax, -8306574491275203288
	mov QWORD PTR [rdi+104], rax
	movabs rax, 4289733633151100261
	mov QWORD PTR [rdi+112], rax
	movabs rax, -3514295694670183664
	mov QWORD PTR [rdi+120], rax
	movabs rax, 2240099277684876711
	mov QWORD PTR [rdi+128], rax
	movabs rax, 1526563086152259251
	mov QWORD PTR [rdi+136], rax
	movabs rax, 1107163671716839903
	mov QWORD PTR [rdi+144], rax
	movabs rax, -8306574491275203288
	mov QWORD PTR [rdi+152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+248], rax
	movabs rax, 1
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
	movabs rax, 8698984072815842221
	mov QWORD PTR [rdi+304], rax
	movabs rax, 5993262882146674062
	mov QWORD PTR [rdi+312], rax
	movabs rax, -1347097566612230436
	mov QWORD PTR [rdi+320], rax
	movabs rax, -1526563086152259253
	mov QWORD PTR [rdi+328], rax
	movabs rax, -1107163671716839904
	mov QWORD PTR [rdi+336], rax
	movabs rax, 8306574491275203287
	mov QWORD PTR [rdi+344], rax
	movabs rax, -2655231979017192295
	mov QWORD PTR [rdi+352], rax
	movabs rax, 8491523898726658171
	mov QWORD PTR [rdi+360], rax
	movabs rax, -7825160784527159884
	mov QWORD PTR [rdi+368], rax
	movabs rax, -1729406561235594380
	mov QWORD PTR [rdi+376], rax
	movabs rax, 4614658957253807200
	mov QWORD PTR [rdi+384], rax
	movabs rax, 8949637766470746321
	mov QWORD PTR [rdi+392], rax
	movabs rax, -3041344086283733004
	mov QWORD PTR [rdi+400], rax
	movabs rax, -740490093907602121
	mov QWORD PTR [rdi+408], rax
	movabs rax, 6227117305712425834
	mov QWORD PTR [rdi+416], rax
	movabs rax, 3500483756195816918
	mov QWORD PTR [rdi+424], rax
	movabs rax, 8231616977324551736
	mov QWORD PTR [rdi+432], rax
	movabs rax, 4827945035257030358
	mov QWORD PTR [rdi+440], rax
	movabs rax, -6806664257334608959
	mov QWORD PTR [rdi+448], rax
	movabs rax, 7420948023505094335
	mov QWORD PTR [rdi+456], rax
	movabs rax, -7727199590878793949
	mov QWORD PTR [rdi+464], rax
	movabs rax, 471512706623218020
	mov QWORD PTR [rdi+472], rax
	movabs rax, -7143538248096350055
	mov QWORD PTR [rdi+480], rax
	movabs rax, -8862955202463580223
	mov QWORD PTR [rdi+488], rax
	movabs rax, -1785480228984766299
	mov QWORD PTR [rdi+496], rax
	movabs rax, -729351938195755179
	mov QWORD PTR [rdi+504], rax
	movabs rax, -539576932270393348
	mov QWORD PTR [rdi+512], rax
	movabs rax, -6809252606470155753
	mov QWORD PTR [rdi+520], rax
	movabs rax, -4173106883367674442
	mov QWORD PTR [rdi+528], rax
	movabs rax, 3239390375920101557
	mov QWORD PTR [rdi+536], rax
	movabs rax, -6030650154532004722
	mov QWORD PTR [rdi+544], rax
	movabs rax, 3973949621338336110
	mov QWORD PTR [rdi+552], rax
	movabs rax, 3067653090611193994
	mov QWORD PTR [rdi+560], rax
	movabs rax, 6289968246193342719
	mov QWORD PTR [rdi+568], rax
	movabs rax, -8104106817701388325
	mov QWORD PTR [rdi+576], rax
	movabs rax, 930156164074608578
	mov QWORD PTR [rdi+584], rax
	movabs rax, -4289733633151100261
	mov QWORD PTR [rdi+592], rax
	movabs rax, 3514295694670183663
	mov QWORD PTR [rdi+600], rax
	movabs rax, -2240099277684876712
	mov QWORD PTR [rdi+608], rax
	movabs rax, -1526563086152259252
	mov QWORD PTR [rdi+616], rax
	movabs rax, -1107163671716839904
	mov QWORD PTR [rdi+624], rax
	movabs rax, 8306574491275203287
	mov QWORD PTR [rdi+632], rax
	movabs rax, -8698984072815842223
	mov QWORD PTR [rdi+640], rax
	movabs rax, -5993262882146674063
	mov QWORD PTR [rdi+648], rax
	movabs rax, 1347097566612230435
	mov QWORD PTR [rdi+656], rax
	movabs rax, 1526563086152259252
	mov QWORD PTR [rdi+664], rax
	movabs rax, 1107163671716839903
	mov QWORD PTR [rdi+672], rax
	movabs rax, -8306574491275203288
	mov QWORD PTR [rdi+680], rax
	movabs rax, 4289733633151100259
	mov QWORD PTR [rdi+688], rax
	movabs rax, -3514295694670183664
	mov QWORD PTR [rdi+696], rax
	movabs rax, 2240099277684876711
	mov QWORD PTR [rdi+704], rax
	movabs rax, 1526563086152259251
	mov QWORD PTR [rdi+712], rax
	movabs rax, 1107163671716839903
	mov QWORD PTR [rdi+720], rax
	movabs rax, -8306574491275203288
	mov QWORD PTR [rdi+728], rax
	movabs rax, 0
	mov QWORD PTR [rdi+736], rax
	movabs rax, 0
	mov QWORD PTR [rdi+744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+752], rax
	movabs rax, 0
	mov QWORD PTR [rdi+760], rax
	movabs rax, 0
	mov QWORD PTR [rdi+768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+776], rax
	movabs rax, 8698984072815842221
	mov QWORD PTR [rdi+784], rax
	movabs rax, 5993262882146674062
	mov QWORD PTR [rdi+792], rax
	movabs rax, -1347097566612230436
	mov QWORD PTR [rdi+800], rax
	movabs rax, -1526563086152259253
	mov QWORD PTR [rdi+808], rax
	movabs rax, -1107163671716839904
	mov QWORD PTR [rdi+816], rax
	movabs rax, 8306574491275203287
	mov QWORD PTR [rdi+824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+840], rax
	movabs rax, 0
	mov QWORD PTR [rdi+848], rax
	movabs rax, 0
	mov QWORD PTR [rdi+856], rax
	movabs rax, 0
	mov QWORD PTR [rdi+864], rax
	movabs rax, 0
	mov QWORD PTR [rdi+872], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2176], rax
	mov rsi, r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+1552]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2224], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2225], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2226], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2227], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2228], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2229], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2230], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2231], dl
	add rbx, 1
	cmp rbx, 48
	jne 20b
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rdi+rbx*1+640]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2616], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2617], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2618], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2619], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2620], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2621], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2622], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2623], dl
	add rbx, 1
	cmp rbx, 48
	jne 21b
	mov ebx, 0
22:
	movzx eax, BYTE PTR [rdi+rbx*1+688]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3008], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3009], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3010], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3011], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3012], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3013], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3014], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3015], dl
	add rbx, 1
	cmp rbx, 48
	jne 22b
	mov rax, QWORD PTR [r10+40]
	bswap rax
	mov QWORD PTR [rdi+1504], rax
	mov rax, QWORD PTR [r10+32]
	bswap rax
	mov QWORD PTR [rdi+1512], rax
	mov rax, QWORD PTR [r10+24]
	bswap rax
	mov QWORD PTR [rdi+1520], rax
	mov rax, QWORD PTR [r10+16]
	bswap rax
	mov QWORD PTR [rdi+1528], rax
	mov rax, QWORD PTR [r10+8]
	bswap rax
	mov QWORD PTR [rdi+1536], rax
	mov rax, QWORD PTR [r10]
	bswap rax
	mov QWORD PTR [rdi+1544], rax
	movabs rax, 611627528996932574
	mov QWORD PTR [rdi+1936], rax
	movabs rax, 6004005513631619429
	mov QWORD PTR [rdi+1944], rax
	movabs rax, -8203032269463222119
	mov QWORD PTR [rdi+1952], rax
	movabs rax, 7067275440101578159
	mov QWORD PTR [rdi+1960], rax
	movabs rax, -3042481458783582932
	mov QWORD PTR [rdi+1968], rax
	movabs rax, 3944986710845028418
	mov QWORD PTR [rdi+1976], rax
	movabs rax, 2235471971536658797
	mov QWORD PTR [rdi+1984], rax
	movabs rax, 3904330365885091811
	mov QWORD PTR [rdi+1992], rax
	movabs rax, -3624176400461631782
	mov QWORD PTR [rdi+2000], rax
	movabs rax, 1675682280782692056
	mov QWORD PTR [rdi+2008], rax
	movabs rax, 3112926883013797213
	mov QWORD PTR [rdi+2016], rax
	movabs rax, 4989371539230459562
	mov QWORD PTR [rdi+2024], rax
	mov rdx, r9
	add rdx, 49
	mov rax, QWORD PTR [rdx+40]
	bswap rax
	mov QWORD PTR [rdi+1792], rax
	mov rax, QWORD PTR [rdx+32]
	bswap rax
	mov QWORD PTR [rdi+1800], rax
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1808], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1816], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1824], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1832], rax
	movzx edx, BYTE PTR [r9]
	xor rdx, 4
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	call {vg_brainpoolp384r1_check_point}
	mov rdx, QWORD PTR [rdi+1552]
	sub rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1560]
	sbb rdx, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+1568]
	sbb rdx, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rdi+1576]
	sbb rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+1584]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+1592]
	sbb rdx, QWORD PTR [rdi+152]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+1552]
	or rdx, QWORD PTR [rdi+1560]
	or rdx, QWORD PTR [rdi+1568]
	or rdx, QWORD PTR [rdi+1576]
	or rdx, QWORD PTR [rdi+1584]
	or rdx, QWORD PTR [rdi+1592]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rdx, QWORD PTR [rdi+1504]
	sub rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1512]
	sbb rdx, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+1520]
	sbb rdx, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rdi+1528]
	sbb rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+1536]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+1544]
	sbb rdx, QWORD PTR [rdi+152]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+1504]
	or rdx, QWORD PTR [rdi+1512]
	or rdx, QWORD PTR [rdi+1520]
	or rdx, QWORD PTR [rdi+1528]
	or rdx, QWORD PTR [rdi+1536]
	or rdx, QWORD PTR [rdi+1544]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1536]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1544]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1840], r14
	mov QWORD PTR [rdi+1848], r15
	mov QWORD PTR [rdi+1856], r8
	mov QWORD PTR [rdi+1864], r9
	mov QWORD PTR [rdi+1872], r10
	mov QWORD PTR [rdi+1880], r11
	call {vg_brainpoolp384r1_inv_mod_n}
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1984], r14
	mov QWORD PTR [rdi+1992], r15
	mov QWORD PTR [rdi+2000], r8
	mov QWORD PTR [rdi+2008], r9
	mov QWORD PTR [rdi+2016], r10
	mov QWORD PTR [rdi+2024], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1552]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1560]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1568]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1576]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1584]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1592]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1936], r14
	mov QWORD PTR [rdi+1944], r15
	mov QWORD PTR [rdi+1952], r8
	mov QWORD PTR [rdi+1960], r9
	mov QWORD PTR [rdi+1968], r10
	mov QWORD PTR [rdi+1976], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2008]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2016]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2024]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+2032], r14
	mov QWORD PTR [rdi+2040], r15
	mov QWORD PTR [rdi+2048], r8
	mov QWORD PTR [rdi+2056], r9
	mov QWORD PTR [rdi+2064], r10
	mov QWORD PTR [rdi+2072], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+2080], r14
	mov QWORD PTR [rdi+2088], r15
	mov QWORD PTR [rdi+2096], r8
	mov QWORD PTR [rdi+2104], r9
	mov QWORD PTR [rdi+2112], r10
	mov QWORD PTR [rdi+2120], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+2032]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+2040]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+2048]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2056]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2064]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2072]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1696], r14
	mov QWORD PTR [rdi+1704], r15
	mov QWORD PTR [rdi+1712], r8
	mov QWORD PTR [rdi+1720], r9
	mov QWORD PTR [rdi+1728], r10
	mov QWORD PTR [rdi+1736], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+2080]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+2088]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+2096]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2104]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2112]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2120]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1744], r14
	mov QWORD PTR [rdi+1752], r15
	mov QWORD PTR [rdi+1760], r8
	mov QWORD PTR [rdi+1768], r9
	mov QWORD PTR [rdi+1776], r10
	mov QWORD PTR [rdi+1784], r11
	mov rax, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+1600], rax
	mov rax, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+1608], rax
	mov rax, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+1616], rax
	mov rax, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+1624], rax
	mov rax, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+1632], rax
	mov rax, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+1640], rax
	mov rax, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+1552], rax
	mov rax, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+1560], rax
	mov rax, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+1568], rax
	mov rax, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rdi+1728]
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rdi+1736]
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+824], rax
	call {vg_brainpoolp384r1_mul}
	mov rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+2032], rax
	mov rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+2040], rax
	mov rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+2048], rax
	mov rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+2056], rax
	mov rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+2064], rax
	mov rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+2072], rax
	mov rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+2080], rax
	mov rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+2088], rax
	mov rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+2096], rax
	mov rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+2104], rax
	mov rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+2112], rax
	mov rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+2120], rax
	mov rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+1840], rax
	mov rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+1848], rax
	mov rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+1856], rax
	mov rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+1864], rax
	mov rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+1872], rax
	mov rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+1880], rax
	movabs rax, 0
	mov QWORD PTR [rdi+736], rax
	movabs rax, 0
	mov QWORD PTR [rdi+744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+752], rax
	movabs rax, 0
	mov QWORD PTR [rdi+760], rax
	movabs rax, 0
	mov QWORD PTR [rdi+768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+776], rax
	movabs rax, 8698984072815842221
	mov QWORD PTR [rdi+784], rax
	movabs rax, 5993262882146674062
	mov QWORD PTR [rdi+792], rax
	movabs rax, -1347097566612230436
	mov QWORD PTR [rdi+800], rax
	movabs rax, -1526563086152259253
	mov QWORD PTR [rdi+808], rax
	movabs rax, -1107163671716839904
	mov QWORD PTR [rdi+816], rax
	movabs rax, 8306574491275203287
	mov QWORD PTR [rdi+824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+840], rax
	movabs rax, 0
	mov QWORD PTR [rdi+848], rax
	movabs rax, 0
	mov QWORD PTR [rdi+856], rax
	movabs rax, 0
	mov QWORD PTR [rdi+864], rax
	movabs rax, 0
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rdi+1744]
	mov QWORD PTR [rdi+1552], rax
	mov rax, QWORD PTR [rdi+1752]
	mov QWORD PTR [rdi+1560], rax
	mov rax, QWORD PTR [rdi+1760]
	mov QWORD PTR [rdi+1568], rax
	mov rax, QWORD PTR [rdi+1768]
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rdi+1776]
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rdi+1888]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rdi+1896]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rdi+1904]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rdi+1912]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rdi+2128]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rdi+2136]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rdi+2144]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rdi+2152]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rdi+2160]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rdi+2168]
	mov QWORD PTR [rdi+824], rax
	call {vg_brainpoolp384r1_mul}
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+2032]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+2040]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+2048]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2056]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2064]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2072]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+2080]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+2088]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+2096]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2104]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2112]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2120]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1216], r14
	mov QWORD PTR [rdi+1224], r15
	mov QWORD PTR [rdi+1232], r8
	mov QWORD PTR [rdi+1240], r9
	mov QWORD PTR [rdi+1248], r10
	mov QWORD PTR [rdi+1256], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8, QWORD PTR [rdi+2032]
	mov r9, QWORD PTR [rdi+2040]
	mov r10, QWORD PTR [rdi+2048]
	mov r11, QWORD PTR [rdi+2056]
	mov r12, QWORD PTR [rdi+2064]
	mov r13, QWORD PTR [rdi+2072]
	mov r14d, 0
	add r8, QWORD PTR [rdi+2080]
	adc r9, QWORD PTR [rdi+2088]
	adc r10, QWORD PTR [rdi+2096]
	adc r11, QWORD PTR [rdi+2104]
	adc r12, QWORD PTR [rdi+2112]
	adc r13, QWORD PTR [rdi+2120]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	mov r14d, 0
	add r8, QWORD PTR [rdi+784]
	adc r9, QWORD PTR [rdi+792]
	adc r10, QWORD PTR [rdi+800]
	adc r11, QWORD PTR [rdi+808]
	adc r12, QWORD PTR [rdi+816]
	adc r13, QWORD PTR [rdi+824]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1312], r14
	mov QWORD PTR [rdi+1320], r15
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov QWORD PTR [rdi+1344], r10
	mov QWORD PTR [rdi+1352], r11
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1216]
	adc r9, QWORD PTR [rdi+1224]
	adc r10, QWORD PTR [rdi+1232]
	adc r11, QWORD PTR [rdi+1240]
	adc r12, QWORD PTR [rdi+1248]
	adc r13, QWORD PTR [rdi+1256]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	sub r8, QWORD PTR [rdi+1360]
	sbb r9, QWORD PTR [rdi+1368]
	sbb r10, QWORD PTR [rdi+1376]
	sbb r11, QWORD PTR [rdi+1384]
	sbb r12, QWORD PTR [rdi+1392]
	sbb r13, QWORD PTR [rdi+1400]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov r8, QWORD PTR [rdi+2032]
	mov r9, QWORD PTR [rdi+2040]
	mov r10, QWORD PTR [rdi+2048]
	mov r11, QWORD PTR [rdi+2056]
	mov r12, QWORD PTR [rdi+2064]
	mov r13, QWORD PTR [rdi+2072]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1840]
	adc r9, QWORD PTR [rdi+1848]
	adc r10, QWORD PTR [rdi+1856]
	adc r11, QWORD PTR [rdi+1864]
	adc r12, QWORD PTR [rdi+1872]
	adc r13, QWORD PTR [rdi+1880]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	mov r14d, 0
	add r8, QWORD PTR [rdi+832]
	adc r9, QWORD PTR [rdi+840]
	adc r10, QWORD PTR [rdi+848]
	adc r11, QWORD PTR [rdi+856]
	adc r12, QWORD PTR [rdi+864]
	adc r13, QWORD PTR [rdi+872]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r14
	mov QWORD PTR [rdi+1368], r15
	mov QWORD PTR [rdi+1376], r8
	mov QWORD PTR [rdi+1384], r9
	mov QWORD PTR [rdi+1392], r10
	mov QWORD PTR [rdi+1400], r11
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov r8, QWORD PTR [rdi+1360]
	mov r9, QWORD PTR [rdi+1368]
	mov r10, QWORD PTR [rdi+1376]
	mov r11, QWORD PTR [rdi+1384]
	mov r12, QWORD PTR [rdi+1392]
	mov r13, QWORD PTR [rdi+1400]
	sub r8, QWORD PTR [rdi+1408]
	sbb r9, QWORD PTR [rdi+1416]
	sbb r10, QWORD PTR [rdi+1424]
	sbb r11, QWORD PTR [rdi+1432]
	sbb r12, QWORD PTR [rdi+1440]
	sbb r13, QWORD PTR [rdi+1448]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8, QWORD PTR [rdi+2080]
	mov r9, QWORD PTR [rdi+2088]
	mov r10, QWORD PTR [rdi+2096]
	mov r11, QWORD PTR [rdi+2104]
	mov r12, QWORD PTR [rdi+2112]
	mov r13, QWORD PTR [rdi+2120]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1840]
	adc r9, QWORD PTR [rdi+1848]
	adc r10, QWORD PTR [rdi+1856]
	adc r11, QWORD PTR [rdi+1864]
	adc r12, QWORD PTR [rdi+1872]
	adc r13, QWORD PTR [rdi+1880]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov r8, QWORD PTR [rdi+784]
	mov r9, QWORD PTR [rdi+792]
	mov r10, QWORD PTR [rdi+800]
	mov r11, QWORD PTR [rdi+808]
	mov r12, QWORD PTR [rdi+816]
	mov r13, QWORD PTR [rdi+824]
	mov r14d, 0
	add r8, QWORD PTR [rdi+832]
	adc r9, QWORD PTR [rdi+840]
	adc r10, QWORD PTR [rdi+848]
	adc r11, QWORD PTR [rdi+856]
	adc r12, QWORD PTR [rdi+864]
	adc r13, QWORD PTR [rdi+872]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r14
	mov QWORD PTR [rdi+1416], r15
	mov QWORD PTR [rdi+1424], r8
	mov QWORD PTR [rdi+1432], r9
	mov QWORD PTR [rdi+1440], r10
	mov QWORD PTR [rdi+1448], r11
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov r8, QWORD PTR [rdi+1408]
	mov r9, QWORD PTR [rdi+1416]
	mov r10, QWORD PTR [rdi+1424]
	mov r11, QWORD PTR [rdi+1432]
	mov r12, QWORD PTR [rdi+1440]
	mov r13, QWORD PTR [rdi+1448]
	sub r8, QWORD PTR [rdi+880]
	sbb r9, QWORD PTR [rdi+888]
	sbb r10, QWORD PTR [rdi+896]
	sbb r11, QWORD PTR [rdi+904]
	sbb r12, QWORD PTR [rdi+912]
	sbb r13, QWORD PTR [rdi+920]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov QWORD PTR [rdi+992], r8
	mov QWORD PTR [rdi+1000], r9
	mov QWORD PTR [rdi+1008], r10
	mov QWORD PTR [rdi+1016], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+880]
	mov r9, QWORD PTR [rdi+888]
	mov r10, QWORD PTR [rdi+896]
	mov r11, QWORD PTR [rdi+904]
	mov r12, QWORD PTR [rdi+912]
	mov r13, QWORD PTR [rdi+920]
	mov r14d, 0
	add r8, QWORD PTR [rdi+976]
	adc r9, QWORD PTR [rdi+984]
	adc r10, QWORD PTR [rdi+992]
	adc r11, QWORD PTR [rdi+1000]
	adc r12, QWORD PTR [rdi+1008]
	adc r13, QWORD PTR [rdi+1016]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov QWORD PTR [rdi+992], r10
	mov QWORD PTR [rdi+1000], r11
	mov QWORD PTR [rdi+1008], r12
	mov QWORD PTR [rdi+1016], r13
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	sub r8, QWORD PTR [rdi+976]
	sbb r9, QWORD PTR [rdi+984]
	sbb r10, QWORD PTR [rdi+992]
	sbb r11, QWORD PTR [rdi+1000]
	sbb r12, QWORD PTR [rdi+1008]
	sbb r13, QWORD PTR [rdi+1016]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+976]
	adc r9, QWORD PTR [rdi+984]
	adc r10, QWORD PTR [rdi+992]
	adc r11, QWORD PTR [rdi+1000]
	adc r12, QWORD PTR [rdi+1008]
	adc r13, QWORD PTR [rdi+1016]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov QWORD PTR [rdi+992], r10
	mov QWORD PTR [rdi+1000], r11
	mov QWORD PTR [rdi+1008], r12
	mov QWORD PTR [rdi+1016], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+880]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+888]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+928], r14
	mov QWORD PTR [rdi+936], r15
	mov QWORD PTR [rdi+944], r8
	mov QWORD PTR [rdi+952], r9
	mov QWORD PTR [rdi+960], r10
	mov QWORD PTR [rdi+968], r11
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r14
	mov QWORD PTR [rdi+1368], r15
	mov QWORD PTR [rdi+1376], r8
	mov QWORD PTR [rdi+1384], r9
	mov QWORD PTR [rdi+1392], r10
	mov QWORD PTR [rdi+1400], r11
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	sub r8, QWORD PTR [rdi+1264]
	sbb r9, QWORD PTR [rdi+1272]
	sbb r10, QWORD PTR [rdi+1280]
	sbb r11, QWORD PTR [rdi+1288]
	sbb r12, QWORD PTR [rdi+1296]
	sbb r13, QWORD PTR [rdi+1304]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	mov QWORD PTR [rdi+1280], r10
	mov QWORD PTR [rdi+1288], r11
	mov QWORD PTR [rdi+1296], r12
	mov QWORD PTR [rdi+1304], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8, QWORD PTR [rdi+1360]
	mov r9, QWORD PTR [rdi+1368]
	mov r10, QWORD PTR [rdi+1376]
	mov r11, QWORD PTR [rdi+1384]
	mov r12, QWORD PTR [rdi+1392]
	mov r13, QWORD PTR [rdi+1400]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1224]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1232]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1240]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1248]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1256]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov r8, QWORD PTR [rdi+928]
	mov r9, QWORD PTR [rdi+936]
	mov r10, QWORD PTR [rdi+944]
	mov r11, QWORD PTR [rdi+952]
	mov r12, QWORD PTR [rdi+960]
	mov r13, QWORD PTR [rdi+968]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+880]
	mov r9, QWORD PTR [rdi+888]
	mov r10, QWORD PTR [rdi+896]
	mov r11, QWORD PTR [rdi+904]
	mov r12, QWORD PTR [rdi+912]
	mov r13, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+1168]
	sbb r9, QWORD PTR [rdi+1176]
	sbb r10, QWORD PTR [rdi+1184]
	sbb r11, QWORD PTR [rdi+1192]
	sbb r12, QWORD PTR [rdi+1200]
	sbb r13, QWORD PTR [rdi+1208]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov QWORD PTR [rdi+992], r8
	mov QWORD PTR [rdi+1000], r9
	mov QWORD PTR [rdi+1008], r10
	mov QWORD PTR [rdi+1016], r11
	mov r8, QWORD PTR [rdi+976]
	mov r9, QWORD PTR [rdi+984]
	mov r10, QWORD PTR [rdi+992]
	mov r11, QWORD PTR [rdi+1000]
	mov r12, QWORD PTR [rdi+1008]
	mov r13, QWORD PTR [rdi+1016]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov QWORD PTR [rdi+992], r10
	mov QWORD PTR [rdi+1000], r11
	mov QWORD PTR [rdi+1008], r12
	mov QWORD PTR [rdi+1016], r13
	mov rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+1552], rax
	mov rax, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+1560], rax
	mov rax, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+1568], rax
	mov rax, QWORD PTR [rdi+1624]
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rdi+1632]
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rdi+1640]
	mov QWORD PTR [rdi+1592], rax
	call {vg_brainpoolp384r1_inv_mod_p}
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+736]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+744]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+752]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+760]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+768]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+776]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1696], r14
	mov QWORD PTR [rdi+1704], r15
	mov QWORD PTR [rdi+1712], r8
	mov QWORD PTR [rdi+1720], r9
	mov QWORD PTR [rdi+1728], r10
	mov QWORD PTR [rdi+1736], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1728]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1736]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1744], r14
	mov QWORD PTR [rdi+1752], r15
	mov QWORD PTR [rdi+1760], r8
	mov QWORD PTR [rdi+1768], r9
	mov QWORD PTR [rdi+1776], r10
	mov QWORD PTR [rdi+1784], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1744]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1752]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1760]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1768]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1776]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1784]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1888], r14
	mov QWORD PTR [rdi+1896], r15
	mov QWORD PTR [rdi+1904], r8
	mov QWORD PTR [rdi+1912], r9
	mov QWORD PTR [rdi+1920], r10
	mov QWORD PTR [rdi+1928], r11
	mov r8, QWORD PTR [rdi+1888]
	mov r9, QWORD PTR [rdi+1896]
	mov r10, QWORD PTR [rdi+1904]
	mov r11, QWORD PTR [rdi+1912]
	mov r12, QWORD PTR [rdi+1920]
	mov r13, QWORD PTR [rdi+1928]
	sub r8, QWORD PTR [rdi+1936]
	sbb r9, QWORD PTR [rdi+1944]
	sbb r10, QWORD PTR [rdi+1952]
	sbb r11, QWORD PTR [rdi+1960]
	sbb r12, QWORD PTR [rdi+1968]
	sbb r13, QWORD PTR [rdi+1976]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+128]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+136]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+144]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+152]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1984], r8
	mov QWORD PTR [rdi+1992], r9
	mov QWORD PTR [rdi+2000], r10
	mov QWORD PTR [rdi+2008], r11
	mov QWORD PTR [rdi+2016], r12
	mov QWORD PTR [rdi+2024], r13
	mov rdx, QWORD PTR [rdi+832]
	or rdx, QWORD PTR [rdi+840]
	or rdx, QWORD PTR [rdi+848]
	or rdx, QWORD PTR [rdi+856]
	or rdx, QWORD PTR [rdi+864]
	or rdx, QWORD PTR [rdi+872]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rdx, QWORD PTR [rdi+1984]
	or rdx, QWORD PTR [rdi+1992]
	or rdx, QWORD PTR [rdi+2000]
	or rdx, QWORD PTR [rdi+2008]
	or rdx, QWORD PTR [rdi+2016]
	or rdx, QWORD PTR [rdi+2024]
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rax, QWORD PTR [rdi+2176]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6
