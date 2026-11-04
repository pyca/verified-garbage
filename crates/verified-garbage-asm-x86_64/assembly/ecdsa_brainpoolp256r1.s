// The functions of `src/ecdsa_brainpoolp256r1.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp256r1_verify:
	mov r8, rcx
	mov r9, rdi
	mov rcx, rdx
	mov r10, rdx
	add r10, 32
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
	mov rax, QWORD PTR [rcx+24]
	bswap rax
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rcx+16]
	bswap rax
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rcx+8]
	bswap rax
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 2311270323689771895
	mov QWORD PTR [rdi+64], rax
	movabs rax, 7943213001558335528
	mov QWORD PTR [rdi+72], rax
	movabs rax, 4496292894210231666
	mov QWORD PTR [rdi+80], rax
	movabs rax, -6198263861319128644
	mov QWORD PTR [rdi+88], rax
	movabs rax, -8061990328899971417
	mov QWORD PTR [rdi+96], rax
	movabs rax, -8342501991185799433
	mov QWORD PTR [rdi+104], rax
	movabs rax, 4496292894210231665
	mov QWORD PTR [rdi+112], rax
	movabs rax, -6198263861319128644
	mov QWORD PTR [rdi+120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+184], rax
	movabs rax, 1
	mov QWORD PTR [rdi+192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+216], rax
	movabs rax, -2311270323689771895
	mov QWORD PTR [rdi+224], rax
	movabs rax, -7943213001558335529
	mov QWORD PTR [rdi+232], rax
	movabs rax, -4496292894210231667
	mov QWORD PTR [rdi+240], rax
	movabs rax, 6198263861319128643
	mov QWORD PTR [rdi+248], rax
	movabs rax, -3039491183301008799
	mov QWORD PTR [rdi+256], rax
	movabs rax, -6448833670171980700
	mov QWORD PTR [rdi+264], rax
	movabs rax, -7643701076807887506
	mov QWORD PTR [rdi+272], rax
	movabs rax, 2181561549916126231
	mov QWORD PTR [rdi+280], rax
	movabs rax, 1258448611663075917
	mov QWORD PTR [rdi+288], rax
	movabs rax, 2326635724976504331
	mov QWORD PTR [rdi+296], rax
	movabs rax, 3341611249364942219
	mov QWORD PTR [rdi+304], rax
	movabs rax, 4800520967890361275
	mov QWORD PTR [rdi+312], rax
	movabs rax, 2864528151195668748
	mov QWORD PTR [rdi+320], rax
	movabs rax, -9160799265092734198
	mov QWORD PTR [rdi+328], rax
	movabs rax, 8091896632905902803
	mov QWORD PTR [rdi+336], rax
	movabs rax, -8205709727035712545
	mov QWORD PTR [rdi+344], rax
	movabs rax, -7327381570567701993
	mov QWORD PTR [rdi+352], rax
	movabs rax, -6478161596457352862
	mov QWORD PTR [rdi+360], rax
	movabs rax, 1656751717988797187
	mov QWORD PTR [rdi+368], rax
	movabs rax, 1507431292125229218
	mov QWORD PTR [rdi+376], rax
	movabs rax, -2172748371355042650
	mov QWORD PTR [rdi+384], rax
	movabs rax, -910545805336320864
	mov QWORD PTR [rdi+392], rax
	movabs rax, -7242027999900377936
	mov QWORD PTR [rdi+400], rax
	movabs rax, 803313888700622690
	mov QWORD PTR [rdi+408], rax
	movabs rax, 8061990328899971417
	mov QWORD PTR [rdi+416], rax
	movabs rax, 8342501991185799432
	mov QWORD PTR [rdi+424], rax
	movabs rax, -4496292894210231666
	mov QWORD PTR [rdi+432], rax
	movabs rax, 6198263861319128643
	mov QWORD PTR [rdi+440], rax
	movabs rax, 2311270323689771893
	mov QWORD PTR [rdi+448], rax
	movabs rax, 7943213001558335528
	mov QWORD PTR [rdi+456], rax
	movabs rax, 4496292894210231666
	mov QWORD PTR [rdi+464], rax
	movabs rax, -6198263861319128644
	mov QWORD PTR [rdi+472], rax
	movabs rax, -8061990328899971419
	mov QWORD PTR [rdi+480], rax
	movabs rax, -8342501991185799433
	mov QWORD PTR [rdi+488], rax
	movabs rax, 4496292894210231665
	mov QWORD PTR [rdi+496], rax
	movabs rax, -6198263861319128644
	mov QWORD PTR [rdi+504], rax
	movabs rax, 0
	mov QWORD PTR [rdi+512], rax
	movabs rax, 0
	mov QWORD PTR [rdi+520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+536], rax
	movabs rax, -2311270323689771895
	mov QWORD PTR [rdi+544], rax
	movabs rax, -7943213001558335529
	mov QWORD PTR [rdi+552], rax
	movabs rax, -4496292894210231667
	mov QWORD PTR [rdi+560], rax
	movabs rax, 6198263861319128643
	mov QWORD PTR [rdi+568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+576], rax
	movabs rax, 0
	mov QWORD PTR [rdi+584], rax
	movabs rax, 0
	mov QWORD PTR [rdi+592], rax
	movabs rax, 0
	mov QWORD PTR [rdi+600], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1472], rax
	mov rsi, r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+1056]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1504], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1505], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1506], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1507], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1508], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1509], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1510], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1511], dl
	add rbx, 1
	cmp rbx, 32
	jne 20b
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rdi+rbx*1+448]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1768], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1769], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1770], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1771], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1772], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1773], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1774], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1775], dl
	add rbx, 1
	cmp rbx, 32
	jne 21b
	mov ebx, 0
22:
	movzx eax, BYTE PTR [rdi+rbx*1+480]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2032], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2033], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2034], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2035], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2036], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2037], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2038], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2039], dl
	add rbx, 1
	cmp rbx, 32
	jne 22b
	mov rax, QWORD PTR [r10+24]
	bswap rax
	mov QWORD PTR [rdi+1024], rax
	mov rax, QWORD PTR [r10+16]
	bswap rax
	mov QWORD PTR [rdi+1032], rax
	mov rax, QWORD PTR [r10+8]
	bswap rax
	mov QWORD PTR [rdi+1040], rax
	mov rax, QWORD PTR [r10]
	bswap rax
	mov QWORD PTR [rdi+1048], rax
	movabs rax, -8286940542151533716
	mov QWORD PTR [rdi+1312], rax
	movabs rax, 6687366224416689997
	mov QWORD PTR [rdi+1320], rax
	movabs rax, -6778802763299371001
	mov QWORD PTR [rdi+1328], rax
	movabs rax, 5122750163719651240
	mov QWORD PTR [rdi+1336], rax
	movabs rax, 419482870554358639
	mov QWORD PTR [rdi+1344], rax
	movabs rax, 775545241658834777
	mov QWORD PTR [rdi+1352], rax
	movabs rax, 7262785107691497945
	mov QWORD PTR [rdi+1360], rax
	movabs rax, 1600173655963453758
	mov QWORD PTR [rdi+1368], rax
	mov rdx, r9
	add rdx, 33
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1240], rax
	movzx edx, BYTE PTR [r9]
	xor rdx, 4
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	call {vg_brainpoolp256r1_check_point}
	mov rdx, QWORD PTR [rdi+1056]
	sub rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+1064]
	sbb rdx, QWORD PTR [rdi+104]
	mov rdx, QWORD PTR [rdi+1072]
	sbb rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1080]
	sbb rdx, QWORD PTR [rdi+120]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+1056]
	or rdx, QWORD PTR [rdi+1064]
	or rdx, QWORD PTR [rdi+1072]
	or rdx, QWORD PTR [rdi+1080]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rdx, QWORD PTR [rdi+1024]
	sub rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+1032]
	sbb rdx, QWORD PTR [rdi+104]
	mov rdx, QWORD PTR [rdi+1040]
	sbb rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1048]
	sbb rdx, QWORD PTR [rdi+120]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+1024]
	or rdx, QWORD PTR [rdi+1032]
	or rdx, QWORD PTR [rdi+1040]
	or rdx, QWORD PTR [rdi+1048]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1024]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+1032]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1040]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1048]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+96]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+104]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+112]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+120]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	call {vg_brainpoolp256r1_inv_mod_n}
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1088]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+1096]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1104]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1112]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+96]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+104]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+112]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+120]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1056]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+1064]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1072]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1080]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+96]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+104]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+112]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+120]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1312], r12
	mov QWORD PTR [rdi+1320], r13
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov ebp, 0
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov ebp, 0
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+96]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+104]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+112]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+120]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1376], r12
	mov QWORD PTR [rdi+1384], r13
	mov QWORD PTR [rdi+1392], r8
	mov QWORD PTR [rdi+1400], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+96]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+104]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+112]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+120]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1408], r12
	mov QWORD PTR [rdi+1416], r13
	mov QWORD PTR [rdi+1424], r8
	mov QWORD PTR [rdi+1432], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+96]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+104]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+112]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+120]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1152], r12
	mov QWORD PTR [rdi+1160], r13
	mov QWORD PTR [rdi+1168], r8
	mov QWORD PTR [rdi+1176], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+1416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+96]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+104]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+112]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+120]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1184], r12
	mov QWORD PTR [rdi+1192], r13
	mov QWORD PTR [rdi+1200], r8
	mov QWORD PTR [rdi+1208], r9
	mov rax, QWORD PTR [rdi+1056]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1064]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1152]
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rdi+1160]
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rdi+1168]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1176]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+568], rax
	call {vg_brainpoolp256r1_mul}
	mov rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+1424], rax
	mov rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+1432], rax
	mov rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+1272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+512], rax
	movabs rax, 0
	mov QWORD PTR [rdi+520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+536], rax
	movabs rax, -2311270323689771895
	mov QWORD PTR [rdi+544], rax
	movabs rax, -7943213001558335529
	mov QWORD PTR [rdi+552], rax
	movabs rax, -4496292894210231667
	mov QWORD PTR [rdi+560], rax
	movabs rax, 6198263861319128643
	mov QWORD PTR [rdi+568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+576], rax
	movabs rax, 0
	mov QWORD PTR [rdi+584], rax
	movabs rax, 0
	mov QWORD PTR [rdi+592], rax
	movabs rax, 0
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rdi+1184]
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rdi+1192]
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rdi+1200]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+568], rax
	call {vg_brainpoolp256r1_mul}
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r8
	mov QWORD PTR [rdi+824], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1408]
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+1416]
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r8
	mov QWORD PTR [rdi+856], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1248]
	mov ebp, 0
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
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+1256]
	mov ebp, 0
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
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1264]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1272]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov r8, QWORD PTR [rdi+1376]
	mov r9, QWORD PTR [rdi+1384]
	mov r10, QWORD PTR [rdi+1392]
	mov r11, QWORD PTR [rdi+1400]
	mov r12d, 0
	add r8, QWORD PTR [rdi+1408]
	adc r9, QWORD PTR [rdi+1416]
	adc r10, QWORD PTR [rdi+1424]
	adc r11, QWORD PTR [rdi+1432]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	mov r12d, 0
	add r8, QWORD PTR [rdi+544]
	adc r9, QWORD PTR [rdi+552]
	adc r10, QWORD PTR [rdi+560]
	adc r11, QWORD PTR [rdi+568]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r8
	mov QWORD PTR [rdi+920], r9
	mov r8, QWORD PTR [rdi+800]
	mov r9, QWORD PTR [rdi+808]
	mov r10, QWORD PTR [rdi+816]
	mov r11, QWORD PTR [rdi+824]
	mov r12d, 0
	add r8, QWORD PTR [rdi+832]
	adc r9, QWORD PTR [rdi+840]
	adc r10, QWORD PTR [rdi+848]
	adc r11, QWORD PTR [rdi+856]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+1376]
	mov r9, QWORD PTR [rdi+1384]
	mov r10, QWORD PTR [rdi+1392]
	mov r11, QWORD PTR [rdi+1400]
	mov r12d, 0
	add r8, QWORD PTR [rdi+1248]
	adc r9, QWORD PTR [rdi+1256]
	adc r10, QWORD PTR [rdi+1264]
	adc r11, QWORD PTR [rdi+1272]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	mov r12d, 0
	add r8, QWORD PTR [rdi+576]
	adc r9, QWORD PTR [rdi+584]
	adc r10, QWORD PTR [rdi+592]
	adc r11, QWORD PTR [rdi+600]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+928]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+936]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+944]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+952]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r8
	mov QWORD PTR [rdi+952], r9
	mov r8, QWORD PTR [rdi+800]
	mov r9, QWORD PTR [rdi+808]
	mov r10, QWORD PTR [rdi+816]
	mov r11, QWORD PTR [rdi+824]
	mov r12d, 0
	add r8, QWORD PTR [rdi+864]
	adc r9, QWORD PTR [rdi+872]
	adc r10, QWORD PTR [rdi+880]
	adc r11, QWORD PTR [rdi+888]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov r8, QWORD PTR [rdi+928]
	mov r9, QWORD PTR [rdi+936]
	mov r10, QWORD PTR [rdi+944]
	mov r11, QWORD PTR [rdi+952]
	sub r8, QWORD PTR [rdi+960]
	sbb r9, QWORD PTR [rdi+968]
	sbb r10, QWORD PTR [rdi+976]
	sbb r11, QWORD PTR [rdi+984]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8, QWORD PTR [rdi+1408]
	mov r9, QWORD PTR [rdi+1416]
	mov r10, QWORD PTR [rdi+1424]
	mov r11, QWORD PTR [rdi+1432]
	mov r12d, 0
	add r8, QWORD PTR [rdi+1248]
	adc r9, QWORD PTR [rdi+1256]
	adc r10, QWORD PTR [rdi+1264]
	adc r11, QWORD PTR [rdi+1272]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov r8, QWORD PTR [rdi+544]
	mov r9, QWORD PTR [rdi+552]
	mov r10, QWORD PTR [rdi+560]
	mov r11, QWORD PTR [rdi+568]
	mov r12d, 0
	add r8, QWORD PTR [rdi+576]
	adc r9, QWORD PTR [rdi+584]
	adc r10, QWORD PTR [rdi+592]
	adc r11, QWORD PTR [rdi+600]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+960]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+608]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+616]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+624]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+632]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+968]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+608]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+616]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+624]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+632]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+976]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+608]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+616]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+624]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+632]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+984]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+608]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+616]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+624]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+632]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov r12d, 0
	add r8, QWORD PTR [rdi+864]
	adc r9, QWORD PTR [rdi+872]
	adc r10, QWORD PTR [rdi+880]
	adc r11, QWORD PTR [rdi+888]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov r8, QWORD PTR [rdi+960]
	mov r9, QWORD PTR [rdi+968]
	mov r10, QWORD PTR [rdi+976]
	mov r11, QWORD PTR [rdi+984]
	sub r8, QWORD PTR [rdi+608]
	sbb r9, QWORD PTR [rdi+616]
	sbb r10, QWORD PTR [rdi+624]
	sbb r11, QWORD PTR [rdi+632]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+256]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+264]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+272]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+280]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+672], r12
	mov QWORD PTR [rdi+680], r13
	mov QWORD PTR [rdi+688], r8
	mov QWORD PTR [rdi+696], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+288]
	mov ebp, 0
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+296]
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+304]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+312]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r8
	mov QWORD PTR [rdi+632], r9
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	mov r12d, 0
	add r8, QWORD PTR [rdi+672]
	adc r9, QWORD PTR [rdi+680]
	adc r10, QWORD PTR [rdi+688]
	adc r11, QWORD PTR [rdi+696]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	sub r8, QWORD PTR [rdi+672]
	sbb r9, QWORD PTR [rdi+680]
	sbb r10, QWORD PTR [rdi+688]
	sbb r11, QWORD PTR [rdi+696]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov r12d, 0
	add r8, QWORD PTR [rdi+672]
	adc r9, QWORD PTR [rdi+680]
	adc r10, QWORD PTR [rdi+688]
	adc r11, QWORD PTR [rdi+696]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+608]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+672]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+680]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+688]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+696]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+616]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+672]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+680]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+688]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+696]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+624]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+672]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+680]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+688]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+696]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+632]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+672]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+680]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+688]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+696]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+640], r12
	mov QWORD PTR [rdi+648], r13
	mov QWORD PTR [rdi+656], r8
	mov QWORD PTR [rdi+664], r9
	mov r8, QWORD PTR [rdi+800]
	mov r9, QWORD PTR [rdi+808]
	mov r10, QWORD PTR [rdi+816]
	mov r11, QWORD PTR [rdi+824]
	mov r12d, 0
	add r8, QWORD PTR [rdi+800]
	adc r9, QWORD PTR [rdi+808]
	adc r10, QWORD PTR [rdi+816]
	adc r11, QWORD PTR [rdi+824]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov r12d, 0
	add r8, QWORD PTR [rdi+800]
	adc r9, QWORD PTR [rdi+808]
	adc r10, QWORD PTR [rdi+816]
	adc r11, QWORD PTR [rdi+824]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+256]
	mov ebp, 0
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+264]
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+272]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+280]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+288]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+296]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+304]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+312]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r8
	mov QWORD PTR [rdi+952], r9
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov r12d, 0
	add r8, QWORD PTR [rdi+864]
	adc r9, QWORD PTR [rdi+872]
	adc r10, QWORD PTR [rdi+880]
	adc r11, QWORD PTR [rdi+888]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov r8, QWORD PTR [rdi+800]
	mov r9, QWORD PTR [rdi+808]
	mov r10, QWORD PTR [rdi+816]
	mov r11, QWORD PTR [rdi+824]
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+256]
	mov ebp, 0
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+264]
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+272]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+280]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov r8, QWORD PTR [rdi+928]
	mov r9, QWORD PTR [rdi+936]
	mov r10, QWORD PTR [rdi+944]
	mov r11, QWORD PTR [rdi+952]
	mov r12d, 0
	add r8, QWORD PTR [rdi+864]
	adc r9, QWORD PTR [rdi+872]
	adc r10, QWORD PTR [rdi+880]
	adc r11, QWORD PTR [rdi+888]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+832]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+840]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+848]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+856]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r8
	mov QWORD PTR [rdi+824], r9
	mov r8, QWORD PTR [rdi+640]
	mov r9, QWORD PTR [rdi+648]
	mov r10, QWORD PTR [rdi+656]
	mov r11, QWORD PTR [rdi+664]
	mov r12d, 0
	add r8, QWORD PTR [rdi+800]
	adc r9, QWORD PTR [rdi+808]
	adc r10, QWORD PTR [rdi+816]
	adc r11, QWORD PTR [rdi+824]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+960]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+968]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+976]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+984]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r8
	mov QWORD PTR [rdi+824], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+608]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+616]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+624]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+632]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+608]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+616]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+624]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+632]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+608]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+616]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+624]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+632]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+608]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+616]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+624]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+632]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r8
	mov QWORD PTR [rdi+632], r9
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+800]
	sbb r9, QWORD PTR [rdi+808]
	sbb r10, QWORD PTR [rdi+816]
	sbb r11, QWORD PTR [rdi+824]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+896]
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+904]
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+912]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+920]
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r8
	mov QWORD PTR [rdi+824], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+960]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+672]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+680]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+688]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+696]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+968]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+672]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+680]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+688]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+696]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+976]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+672]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+680]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+688]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+696]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+984]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+672]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+680]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+688]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+696]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+672], r12
	mov QWORD PTR [rdi+680], r13
	mov QWORD PTR [rdi+688], r8
	mov QWORD PTR [rdi+696], r9
	mov r8, QWORD PTR [rdi+672]
	mov r9, QWORD PTR [rdi+680]
	mov r10, QWORD PTR [rdi+688]
	mov r11, QWORD PTR [rdi+696]
	mov r12d, 0
	add r8, QWORD PTR [rdi+800]
	adc r9, QWORD PTR [rdi+808]
	adc r10, QWORD PTR [rdi+816]
	adc r11, QWORD PTR [rdi+824]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	mov rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+1080], rax
	call {vg_brainpoolp256r1_inv_mod_p}
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+512]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+520]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+528]
	mov ebp, 0
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+536]
	mov ebp, 0
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1152], r12
	mov QWORD PTR [rdi+1160], r13
	mov QWORD PTR [rdi+1168], r8
	mov QWORD PTR [rdi+1176], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -4132240052652766791
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -4132240052652766791
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -4132240052652766791
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -4132240052652766791
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1184], r12
	mov QWORD PTR [rdi+1192], r13
	mov QWORD PTR [rdi+1200], r8
	mov QWORD PTR [rdi+1208], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
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
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+96]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+104]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+112]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+120]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1280], r12
	mov QWORD PTR [rdi+1288], r13
	mov QWORD PTR [rdi+1296], r8
	mov QWORD PTR [rdi+1304], r9
	mov r8, QWORD PTR [rdi+1280]
	mov r9, QWORD PTR [rdi+1288]
	mov r10, QWORD PTR [rdi+1296]
	mov r11, QWORD PTR [rdi+1304]
	sub r8, QWORD PTR [rdi+1312]
	sbb r9, QWORD PTR [rdi+1320]
	sbb r10, QWORD PTR [rdi+1328]
	sbb r11, QWORD PTR [rdi+1336]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+1344], r8
	mov QWORD PTR [rdi+1352], r9
	mov QWORD PTR [rdi+1360], r10
	mov QWORD PTR [rdi+1368], r11
	mov rdx, QWORD PTR [rdi+576]
	or rdx, QWORD PTR [rdi+584]
	or rdx, QWORD PTR [rdi+592]
	or rdx, QWORD PTR [rdi+600]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rdx, QWORD PTR [rdi+1344]
	or rdx, QWORD PTR [rdi+1352]
	or rdx, QWORD PTR [rdi+1360]
	or rdx, QWORD PTR [rdi+1368]
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+1472]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6

vg_ecdsa_brainpoolp256r1_sign:
	mov rcx, r8
	mov r11, QWORD PTR [r9+24]
	cmp r11, 0
	je 20f
	cmp r11, 1
	je 22f
	cmp r11, 2
	je 24f
	cmp r11, 3
	je 26f
	cmp r11, 4
	je 28f
	cmp r11, 5
	je 210f
	cmp r11, 6
	je 212f
	push r9
	push rdi
	push rsi
	push rdx
	push rcx
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rsi, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rsp+64], rax
	movabs rdx, -8061990328899971417
	sub rax, rdx
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rsp+72], rax
	movabs rdx, -8342501991185799433
	sbb rax, rdx
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rsp+80], rax
	movabs rdx, 4496292894210231665
	sbb rax, rdx
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rsp+88], rax
	movabs rdx, -6198263861319128644
	sbb rax, rdx
	mov QWORD PTR [rsp+24], rax
	sbb rdx, rdx
	mov rax, QWORD PTR [rsp+64]
	mov rcx, QWORD PTR [rsp]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+8]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+144], rax
	mov rax, QWORD PTR [rsp+80]
	mov rcx, QWORD PTR [rsp+16]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+136], rax
	mov rax, QWORD PTR [rsp+88]
	mov rcx, QWORD PTR [rsp+24]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+128], rax
	movabs rax, 72340172838076673
	xor ecx, ecx
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+56], rcx
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov eax, 0
	mov BYTE PTR [rdi+2288], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2289], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2297], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2305], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2313], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+2345], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 97
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 225
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 160
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 160
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 160
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+88], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov eax, 1
	mov BYTE PTR [rdi+2288], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2289], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2297], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2305], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2313], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+2345], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 97
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 225
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 160
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 160
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 160
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+88], rax
	mov eax, 128
	mov QWORD PTR [rsp+176], rax
214:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 160
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 160
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+88], rax
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+192]
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_brainpoolp256r1_sign_k}
	mov rcx, QWORD PTR [rsp+176]
	sub rcx, 1
	mov QWORD PTR [rsp+176], rcx
	cmp eax, 1
	sbb rdx, rdx
	and rdx, rcx
	test rdx, rdx
	jne 215f
	xor edx, edx
	jmp 216f
215:
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov eax, 0
	mov BYTE PTR [rdi+2288], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 33
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 161
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 160
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 160
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 160
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+88], rax
	mov edx, 1
	test rdx, rdx
216:
	jne 214b
	xor ecx, ecx
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], rcx
	mov QWORD PTR [rsp+80], rcx
	mov QWORD PTR [rsp+88], rcx
	mov QWORD PTR [rsp+96], rcx
	mov QWORD PTR [rsp+104], rcx
	mov QWORD PTR [rsp+112], rcx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+144], rcx
	mov QWORD PTR [rsp+152], rcx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+168], rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	jmp 213f
212:
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rdi
	push rsi
	push rdx
	push rcx
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rsi, QWORD PTR [rsp+192]
	mov rdi, QWORD PTR [rsp+184]
	xor eax, eax
	mov QWORD PTR [rsp+216], rax
	xor eax, eax
	mov QWORD PTR [rsp+224], rax
	xor eax, eax
	mov QWORD PTR [rsp+232], rax
	xor eax, eax
	mov QWORD PTR [rsp+240], rax
	xor eax, eax
	mov QWORD PTR [rsp+248], rax
	xor eax, eax
	mov QWORD PTR [rsp+256], rax
	xor eax, eax
	mov QWORD PTR [rsp+264], rax
	xor eax, eax
	mov QWORD PTR [rsp+272], rax
	xor eax, eax
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rsp+220], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsp+228], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rsp+236], rax
	mov rax, QWORD PTR [rsi+20]
	mov QWORD PTR [rsp+240], rax
	movabs rax, 72340172838076673
	xor ecx, ecx
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+56], rcx
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+84]
	mov QWORD PTR [rdi+2276], rax
	mov eax, 0
	mov BYTE PTR [rdi+2284], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2285], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2293], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2301], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2309], rax
	mov rax, QWORD PTR [rsp+216]
	mov QWORD PTR [rdi+2317], rax
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rdi+2325], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi+2333], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rdi+2341], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 93
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 221
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 156
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1940]
	mov QWORD PTR [rsp+20], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 156
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 156
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1940]
	mov QWORD PTR [rsp+84], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+84]
	mov QWORD PTR [rdi+2276], rax
	mov eax, 1
	mov BYTE PTR [rdi+2284], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2285], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2293], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2301], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2309], rax
	mov rax, QWORD PTR [rsp+216]
	mov QWORD PTR [rdi+2317], rax
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rdi+2325], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi+2333], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rdi+2341], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 93
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 221
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 156
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1940]
	mov QWORD PTR [rsp+20], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 156
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 156
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1940]
	mov QWORD PTR [rsp+84], rax
	mov eax, 128
	mov QWORD PTR [rsp+176], rax
217:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 156
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 156
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1940]
	mov QWORD PTR [rsp+84], rax
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+360], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+368], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rsp+376], rax
	mov rax, QWORD PTR [rsp+84]
	mov QWORD PTR [rsp+380], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 156
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 156
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1940]
	mov QWORD PTR [rsp+84], rax
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+388], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+396], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rsp+404], rax
	mov rax, QWORD PTR [rsp+84]
	mov QWORD PTR [rsp+408], rax
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, rsp
	add rdx, 216
	mov rcx, rsp
	add rcx, 360
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_brainpoolp256r1_sign_k}
	mov rcx, QWORD PTR [rsp+176]
	sub rcx, 1
	mov QWORD PTR [rsp+176], rcx
	cmp eax, 1
	sbb rdx, rdx
	and rdx, rcx
	test rdx, rdx
	jne 218f
	xor edx, edx
	jmp 219f
218:
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+84]
	mov QWORD PTR [rdi+2276], rax
	mov eax, 0
	mov BYTE PTR [rdi+2284], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 29
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 157
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 156
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1940]
	mov QWORD PTR [rsp+20], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 156
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 156
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1940]
	mov QWORD PTR [rsp+84], rax
	mov edx, 1
	test rdx, rdx
219:
	jne 217b
	xor ecx, ecx
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], rcx
	mov QWORD PTR [rsp+80], rcx
	mov QWORD PTR [rsp+88], rcx
	mov QWORD PTR [rsp+96], rcx
	mov QWORD PTR [rsp+104], rcx
	mov QWORD PTR [rsp+112], rcx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+144], rcx
	mov QWORD PTR [rsp+152], rcx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+168], rcx
	mov QWORD PTR [rsp+216], rcx
	mov QWORD PTR [rsp+224], rcx
	mov QWORD PTR [rsp+232], rcx
	mov QWORD PTR [rsp+240], rcx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rcx
	mov QWORD PTR [rsp+264], rcx
	mov QWORD PTR [rsp+272], rcx
	mov QWORD PTR [rsp+280], rcx
	mov QWORD PTR [rsp+288], rcx
	mov QWORD PTR [rsp+296], rcx
	mov QWORD PTR [rsp+304], rcx
	mov QWORD PTR [rsp+312], rcx
	mov QWORD PTR [rsp+320], rcx
	mov QWORD PTR [rsp+328], rcx
	mov QWORD PTR [rsp+336], rcx
	mov QWORD PTR [rsp+344], rcx
	mov QWORD PTR [rsp+352], rcx
	mov QWORD PTR [rsp+360], rcx
	mov QWORD PTR [rsp+368], rcx
	mov QWORD PTR [rsp+376], rcx
	mov QWORD PTR [rsp+384], rcx
	mov QWORD PTR [rsp+392], rcx
	mov QWORD PTR [rsp+400], rcx
	mov QWORD PTR [rsp+408], rcx
	mov QWORD PTR [rsp+416], rcx
	mov QWORD PTR [rsp+424], rcx
	mov QWORD PTR [rsp+432], rcx
	mov QWORD PTR [rsp+440], rcx
	mov QWORD PTR [rsp+448], rcx
	mov QWORD PTR [rsp+456], rcx
	mov QWORD PTR [rsp+464], rcx
	mov QWORD PTR [rsp+472], rcx
	mov QWORD PTR [rsp+480], rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
213:
	jmp 211f
210:
	push r9
	push rdi
	push rsi
	push rdx
	push rcx
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rsi, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rsp+64], rax
	movabs rdx, -8061990328899971417
	sub rax, rdx
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rsp+72], rax
	movabs rdx, -8342501991185799433
	sbb rax, rdx
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rsp+80], rax
	movabs rdx, 4496292894210231665
	sbb rax, rdx
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rsp+88], rax
	movabs rdx, -6198263861319128644
	sbb rax, rdx
	mov QWORD PTR [rsp+24], rax
	sbb rdx, rdx
	mov rax, QWORD PTR [rsp+64]
	mov rcx, QWORD PTR [rsp]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+8]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+144], rax
	mov rax, QWORD PTR [rsp+80]
	mov rcx, QWORD PTR [rsp+16]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+136], rax
	mov rax, QWORD PTR [rsp+88]
	mov rcx, QWORD PTR [rsp+24]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+128], rax
	movabs rax, 72340172838076673
	xor ecx, ecx
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+56], rcx
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 0
	mov BYTE PTR [rdi+2320], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2345], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rdi+2353], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rdi+2361], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdi+2369], rax
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+2377], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov eax, DWORD PTR [rsp+48]
	xor eax, ecx
	mov DWORD PTR [rdi+1840], eax
	mov eax, DWORD PTR [rsp+52]
	xor eax, ecx
	mov DWORD PTR [rdi+1844], eax
	mov eax, DWORD PTR [rsp+56]
	xor eax, ecx
	mov DWORD PTR [rdi+1848], eax
	mov eax, DWORD PTR [rsp+60]
	xor eax, ecx
	mov DWORD PTR [rdi+1852], eax
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov eax, DWORD PTR [rsp+48]
	xor eax, ecx
	mov DWORD PTR [rdi+1840], eax
	mov eax, DWORD PTR [rsp+52]
	xor eax, ecx
	mov DWORD PTR [rdi+1844], eax
	mov eax, DWORD PTR [rsp+56]
	xor eax, ecx
	mov DWORD PTR [rdi+1848], eax
	mov eax, DWORD PTR [rsp+60]
	xor eax, ecx
	mov DWORD PTR [rdi+1852], eax
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 129
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 257
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 192
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rdi+1952]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rdi+1960]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rdi+1968]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rdi+1976]
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov eax, DWORD PTR [rsp+48]
	xor eax, ecx
	mov DWORD PTR [rdi+1840], eax
	mov eax, DWORD PTR [rsp+52]
	xor eax, ecx
	mov DWORD PTR [rdi+1844], eax
	mov eax, DWORD PTR [rsp+56]
	xor eax, ecx
	mov DWORD PTR [rdi+1848], eax
	mov eax, DWORD PTR [rsp+60]
	xor eax, ecx
	mov DWORD PTR [rdi+1852], eax
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov eax, DWORD PTR [rsp+48]
	xor eax, ecx
	mov DWORD PTR [rdi+1840], eax
	mov eax, DWORD PTR [rsp+52]
	xor eax, ecx
	mov DWORD PTR [rdi+1844], eax
	mov eax, DWORD PTR [rsp+56]
	xor eax, ecx
	mov DWORD PTR [rdi+1848], eax
	mov eax, DWORD PTR [rsp+60]
	xor eax, ecx
	mov DWORD PTR [rdi+1852], eax
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 192
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 192
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rdi+1952]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rdi+1960]
	mov QWORD PTR [rsp+104], rax
	mov rax, QWORD PTR [rdi+1968]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rdi+1976]
	mov QWORD PTR [rsp+120], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 1
	mov BYTE PTR [rdi+2320], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2345], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rdi+2353], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rdi+2361], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdi+2369], rax
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+2377], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 129
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 257
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 192
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rdi+1952]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rdi+1960]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rdi+1968]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rdi+1976]
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov eax, DWORD PTR [rsp+48]
	xor eax, ecx
	mov DWORD PTR [rdi+1840], eax
	mov eax, DWORD PTR [rsp+52]
	xor eax, ecx
	mov DWORD PTR [rdi+1844], eax
	mov eax, DWORD PTR [rsp+56]
	xor eax, ecx
	mov DWORD PTR [rdi+1848], eax
	mov eax, DWORD PTR [rsp+60]
	xor eax, ecx
	mov DWORD PTR [rdi+1852], eax
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov eax, DWORD PTR [rsp+48]
	xor eax, ecx
	mov DWORD PTR [rdi+1840], eax
	mov eax, DWORD PTR [rsp+52]
	xor eax, ecx
	mov DWORD PTR [rdi+1844], eax
	mov eax, DWORD PTR [rsp+56]
	xor eax, ecx
	mov DWORD PTR [rdi+1848], eax
	mov eax, DWORD PTR [rsp+60]
	xor eax, ecx
	mov DWORD PTR [rdi+1852], eax
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 192
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 192
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rdi+1952]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rdi+1960]
	mov QWORD PTR [rsp+104], rax
	mov rax, QWORD PTR [rdi+1968]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rdi+1976]
	mov QWORD PTR [rsp+120], rax
	mov eax, 128
	mov QWORD PTR [rsp+176], rax
220:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 192
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 192
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rdi+1952]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rdi+1960]
	mov QWORD PTR [rsp+104], rax
	mov rax, QWORD PTR [rdi+1968]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rdi+1976]
	mov QWORD PTR [rsp+120], rax
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+192]
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_brainpoolp256r1_sign_k}
	mov rcx, QWORD PTR [rsp+176]
	sub rcx, 1
	mov QWORD PTR [rsp+176], rcx
	cmp eax, 1
	sbb rdx, rdx
	and rdx, rcx
	test rdx, rdx
	jne 221f
	xor edx, edx
	jmp 222f
221:
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 0
	mov BYTE PTR [rdi+2320], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov eax, DWORD PTR [rsp+48]
	xor eax, ecx
	mov DWORD PTR [rdi+1840], eax
	mov eax, DWORD PTR [rsp+52]
	xor eax, ecx
	mov DWORD PTR [rdi+1844], eax
	mov eax, DWORD PTR [rsp+56]
	xor eax, ecx
	mov DWORD PTR [rdi+1848], eax
	mov eax, DWORD PTR [rsp+60]
	xor eax, ecx
	mov DWORD PTR [rdi+1852], eax
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov eax, DWORD PTR [rsp+48]
	xor eax, ecx
	mov DWORD PTR [rdi+1840], eax
	mov eax, DWORD PTR [rsp+52]
	xor eax, ecx
	mov DWORD PTR [rdi+1844], eax
	mov eax, DWORD PTR [rsp+56]
	xor eax, ecx
	mov DWORD PTR [rdi+1848], eax
	mov eax, DWORD PTR [rsp+60]
	xor eax, ecx
	mov DWORD PTR [rdi+1852], eax
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 65
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 193
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 192
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rdi+1952]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rdi+1960]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rdi+1968]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rdi+1976]
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov eax, DWORD PTR [rsp+48]
	xor eax, ecx
	mov DWORD PTR [rdi+1840], eax
	mov eax, DWORD PTR [rsp+52]
	xor eax, ecx
	mov DWORD PTR [rdi+1844], eax
	mov eax, DWORD PTR [rsp+56]
	xor eax, ecx
	mov DWORD PTR [rdi+1848], eax
	mov eax, DWORD PTR [rsp+60]
	xor eax, ecx
	mov DWORD PTR [rdi+1852], eax
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov eax, DWORD PTR [rsp+48]
	xor eax, ecx
	mov DWORD PTR [rdi+1840], eax
	mov eax, DWORD PTR [rsp+52]
	xor eax, ecx
	mov DWORD PTR [rdi+1844], eax
	mov eax, DWORD PTR [rsp+56]
	xor eax, ecx
	mov DWORD PTR [rdi+1848], eax
	mov eax, DWORD PTR [rsp+60]
	xor eax, ecx
	mov DWORD PTR [rdi+1852], eax
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 192
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 192
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rdi+1952]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rdi+1960]
	mov QWORD PTR [rsp+104], rax
	mov rax, QWORD PTR [rdi+1968]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rdi+1976]
	mov QWORD PTR [rsp+120], rax
	mov edx, 1
	test rdx, rdx
222:
	jne 220b
	xor ecx, ecx
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], rcx
	mov QWORD PTR [rsp+80], rcx
	mov QWORD PTR [rsp+88], rcx
	mov QWORD PTR [rsp+96], rcx
	mov QWORD PTR [rsp+104], rcx
	mov QWORD PTR [rsp+112], rcx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+144], rcx
	mov QWORD PTR [rsp+152], rcx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+168], rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
211:
	jmp 29f
28:
	push r9
	push rdi
	push rsi
	push rdx
	push rcx
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rsi, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rsp+64], rax
	movabs rdx, -8061990328899971417
	sub rax, rdx
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rsp+72], rax
	movabs rdx, -8342501991185799433
	sbb rax, rdx
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rsp+80], rax
	movabs rdx, 4496292894210231665
	sbb rax, rdx
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rsp+88], rax
	movabs rdx, -6198263861319128644
	sbb rax, rdx
	mov QWORD PTR [rsp+24], rax
	sbb rdx, rdx
	mov rax, QWORD PTR [rsp+64]
	mov rcx, QWORD PTR [rsp]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+8]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+144], rax
	mov rax, QWORD PTR [rsp+80]
	mov rcx, QWORD PTR [rsp+16]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+136], rax
	mov rax, QWORD PTR [rsp+88]
	mov rcx, QWORD PTR [rsp+24]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+128], rax
	movabs rax, 72340172838076673
	xor ecx, ecx
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+56], rcx
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov eax, 0
	mov BYTE PTR [rdi+2304], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2305], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2313], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rdi+2345], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdi+2353], rax
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+2361], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 113
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 241
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 48
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 176
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rdi+1952]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rdi+1960]
	mov QWORD PTR [rsp+40], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 48
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 176
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 48
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 176
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rdi+1952]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rdi+1960]
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov eax, 1
	mov BYTE PTR [rdi+2304], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2305], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2313], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rdi+2345], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdi+2353], rax
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+2361], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 113
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 241
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 48
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 176
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rdi+1952]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rdi+1960]
	mov QWORD PTR [rsp+40], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 48
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 176
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 48
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 176
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rdi+1952]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rdi+1960]
	mov QWORD PTR [rsp+104], rax
	mov eax, 128
	mov QWORD PTR [rsp+176], rax
223:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 48
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 176
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 48
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 176
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rdi+1952]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rdi+1960]
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+192]
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_brainpoolp256r1_sign_k}
	mov rcx, QWORD PTR [rsp+176]
	sub rcx, 1
	mov QWORD PTR [rsp+176], rcx
	cmp eax, 1
	sbb rdx, rdx
	and rdx, rcx
	test rdx, rdx
	jne 224f
	xor edx, edx
	jmp 225f
224:
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov eax, 0
	mov BYTE PTR [rdi+2304], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 49
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 177
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 48
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 176
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rdi+1952]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rdi+1960]
	mov QWORD PTR [rsp+40], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov eax, DWORD PTR [rsp+32]
	xor eax, ecx
	mov DWORD PTR [rdi+1824], eax
	mov eax, DWORD PTR [rsp+36]
	xor eax, ecx
	mov DWORD PTR [rdi+1828], eax
	mov eax, DWORD PTR [rsp+40]
	xor eax, ecx
	mov DWORD PTR [rdi+1832], eax
	mov eax, DWORD PTR [rsp+44]
	xor eax, ecx
	mov DWORD PTR [rdi+1836], eax
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov DWORD PTR [rdi+1856], ecx
	mov DWORD PTR [rdi+1860], ecx
	mov DWORD PTR [rdi+1864], ecx
	mov DWORD PTR [rdi+1868], ecx
	mov DWORD PTR [rdi+1872], ecx
	mov DWORD PTR [rdi+1876], ecx
	mov DWORD PTR [rdi+1880], ecx
	mov DWORD PTR [rdi+1884], ecx
	mov DWORD PTR [rdi+1888], ecx
	mov DWORD PTR [rdi+1892], ecx
	mov DWORD PTR [rdi+1896], ecx
	mov DWORD PTR [rdi+1900], ecx
	mov DWORD PTR [rdi+1904], ecx
	mov DWORD PTR [rdi+1908], ecx
	mov DWORD PTR [rdi+1912], ecx
	mov DWORD PTR [rdi+1916], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 128
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 48
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 176
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 48
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 176
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rdi+1952]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rdi+1960]
	mov QWORD PTR [rsp+104], rax
	mov edx, 1
	test rdx, rdx
225:
	jne 223b
	xor ecx, ecx
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], rcx
	mov QWORD PTR [rsp+80], rcx
	mov QWORD PTR [rsp+88], rcx
	mov QWORD PTR [rsp+96], rcx
	mov QWORD PTR [rsp+104], rcx
	mov QWORD PTR [rsp+112], rcx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+144], rcx
	mov QWORD PTR [rsp+152], rcx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+168], rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
29:
	jmp 27f
26:
	push r9
	push rdi
	push rsi
	push rdx
	push rcx
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rsi, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rsp+64], rax
	movabs rdx, -8061990328899971417
	sub rax, rdx
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rsp+72], rax
	movabs rdx, -8342501991185799433
	sbb rax, rdx
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rsp+80], rax
	movabs rdx, 4496292894210231665
	sbb rax, rdx
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rsp+88], rax
	movabs rdx, -6198263861319128644
	sbb rax, rdx
	mov QWORD PTR [rsp+24], rax
	sbb rdx, rdx
	mov rax, QWORD PTR [rsp+64]
	mov rcx, QWORD PTR [rsp]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+8]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+144], rax
	mov rax, QWORD PTR [rsp+80]
	mov rcx, QWORD PTR [rsp+16]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+136], rax
	mov rax, QWORD PTR [rsp+88]
	mov rcx, QWORD PTR [rsp+24]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+128], rax
	movabs rax, 72340172838076673
	xor ecx, ecx
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+56], rcx
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov eax, 0
	mov BYTE PTR [rdi+2288], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2289], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2297], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2305], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2313], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+2345], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 97
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 161
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+88], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov eax, 1
	mov BYTE PTR [rdi+2288], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2289], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2297], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2305], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2313], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+2345], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 97
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 161
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+88], rax
	mov eax, 128
	mov QWORD PTR [rsp+176], rax
226:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+88], rax
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+192]
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_brainpoolp256r1_sign_k}
	mov rcx, QWORD PTR [rsp+176]
	sub rcx, 1
	mov QWORD PTR [rsp+176], rcx
	cmp eax, 1
	sbb rdx, rdx
	and rdx, rcx
	test rdx, rdx
	jne 227f
	xor edx, edx
	jmp 228f
227:
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov eax, 0
	mov BYTE PTR [rdi+2288], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 33
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 97
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov eax, DWORD PTR [rsp+28]
	xor eax, ecx
	mov DWORD PTR [rdi+1820], eax
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1944]
	mov QWORD PTR [rsp+88], rax
	mov edx, 1
	test rdx, rdx
228:
	jne 226b
	xor ecx, ecx
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], rcx
	mov QWORD PTR [rsp+80], rcx
	mov QWORD PTR [rsp+88], rcx
	mov QWORD PTR [rsp+96], rcx
	mov QWORD PTR [rsp+104], rcx
	mov QWORD PTR [rsp+112], rcx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+144], rcx
	mov QWORD PTR [rsp+152], rcx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+168], rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
27:
	jmp 25f
24:
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rdi
	push rsi
	push rdx
	push rcx
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rsi, QWORD PTR [rsp+192]
	mov rdi, QWORD PTR [rsp+184]
	xor eax, eax
	mov QWORD PTR [rsp+216], rax
	xor eax, eax
	mov QWORD PTR [rsp+224], rax
	xor eax, eax
	mov QWORD PTR [rsp+232], rax
	xor eax, eax
	mov QWORD PTR [rsp+240], rax
	xor eax, eax
	mov QWORD PTR [rsp+248], rax
	xor eax, eax
	mov QWORD PTR [rsp+256], rax
	xor eax, eax
	mov QWORD PTR [rsp+264], rax
	xor eax, eax
	mov QWORD PTR [rsp+272], rax
	xor eax, eax
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rsp+220], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsp+228], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rsp+236], rax
	mov rax, QWORD PTR [rsi+20]
	mov QWORD PTR [rsp+240], rax
	movabs rax, 72340172838076673
	xor ecx, ecx
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+56], rcx
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+84]
	mov QWORD PTR [rdi+2276], rax
	mov eax, 0
	mov BYTE PTR [rdi+2284], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2285], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2293], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2301], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2309], rax
	mov rax, QWORD PTR [rsp+216]
	mov QWORD PTR [rdi+2317], rax
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rdi+2325], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi+2333], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rdi+2341], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 93
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 157
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 92
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1940]
	mov QWORD PTR [rsp+20], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 92
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 92
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1940]
	mov QWORD PTR [rsp+84], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+84]
	mov QWORD PTR [rdi+2276], rax
	mov eax, 1
	mov BYTE PTR [rdi+2284], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2285], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2293], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2301], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2309], rax
	mov rax, QWORD PTR [rsp+216]
	mov QWORD PTR [rdi+2317], rax
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rdi+2325], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi+2333], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rdi+2341], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 93
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 157
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 92
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1940]
	mov QWORD PTR [rsp+20], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 92
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 92
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1940]
	mov QWORD PTR [rsp+84], rax
	mov eax, 128
	mov QWORD PTR [rsp+176], rax
229:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 92
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 92
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1940]
	mov QWORD PTR [rsp+84], rax
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+360], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+368], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rsp+376], rax
	mov rax, QWORD PTR [rsp+84]
	mov QWORD PTR [rsp+380], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 92
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 92
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1940]
	mov QWORD PTR [rsp+84], rax
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+388], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+396], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rsp+404], rax
	mov rax, QWORD PTR [rsp+84]
	mov QWORD PTR [rsp+408], rax
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, rsp
	add rdx, 216
	mov rcx, rsp
	add rcx, 360
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_brainpoolp256r1_sign_k}
	mov rcx, QWORD PTR [rsp+176]
	sub rcx, 1
	mov QWORD PTR [rsp+176], rcx
	cmp eax, 1
	sbb rdx, rdx
	and rdx, rcx
	test rdx, rdx
	jne 230f
	xor edx, edx
	jmp 231f
230:
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+84]
	mov QWORD PTR [rdi+2276], rax
	mov eax, 0
	mov BYTE PTR [rdi+2284], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 29
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 93
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 92
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rdi+1940]
	mov QWORD PTR [rsp+20], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov eax, DWORD PTR [rsp+20]
	xor eax, ecx
	mov DWORD PTR [rdi+1812], eax
	mov eax, DWORD PTR [rsp+24]
	xor eax, ecx
	mov DWORD PTR [rdi+1816], eax
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 92
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 28
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 92
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1936]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rdi+1940]
	mov QWORD PTR [rsp+84], rax
	mov edx, 1
	test rdx, rdx
231:
	jne 229b
	xor ecx, ecx
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], rcx
	mov QWORD PTR [rsp+80], rcx
	mov QWORD PTR [rsp+88], rcx
	mov QWORD PTR [rsp+96], rcx
	mov QWORD PTR [rsp+104], rcx
	mov QWORD PTR [rsp+112], rcx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+144], rcx
	mov QWORD PTR [rsp+152], rcx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+168], rcx
	mov QWORD PTR [rsp+216], rcx
	mov QWORD PTR [rsp+224], rcx
	mov QWORD PTR [rsp+232], rcx
	mov QWORD PTR [rsp+240], rcx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rcx
	mov QWORD PTR [rsp+264], rcx
	mov QWORD PTR [rsp+272], rcx
	mov QWORD PTR [rsp+280], rcx
	mov QWORD PTR [rsp+288], rcx
	mov QWORD PTR [rsp+296], rcx
	mov QWORD PTR [rsp+304], rcx
	mov QWORD PTR [rsp+312], rcx
	mov QWORD PTR [rsp+320], rcx
	mov QWORD PTR [rsp+328], rcx
	mov QWORD PTR [rsp+336], rcx
	mov QWORD PTR [rsp+344], rcx
	mov QWORD PTR [rsp+352], rcx
	mov QWORD PTR [rsp+360], rcx
	mov QWORD PTR [rsp+368], rcx
	mov QWORD PTR [rsp+376], rcx
	mov QWORD PTR [rsp+384], rcx
	mov QWORD PTR [rsp+392], rcx
	mov QWORD PTR [rsp+400], rcx
	mov QWORD PTR [rsp+408], rcx
	mov QWORD PTR [rsp+416], rcx
	mov QWORD PTR [rsp+424], rcx
	mov QWORD PTR [rsp+432], rcx
	mov QWORD PTR [rsp+440], rcx
	mov QWORD PTR [rsp+448], rcx
	mov QWORD PTR [rsp+456], rcx
	mov QWORD PTR [rsp+464], rcx
	mov QWORD PTR [rsp+472], rcx
	mov QWORD PTR [rsp+480], rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
25:
	jmp 23f
22:
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rdi
	push rsi
	push rdx
	push rcx
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rsi, QWORD PTR [rsp+192]
	mov rdi, QWORD PTR [rsp+184]
	xor eax, eax
	mov QWORD PTR [rsp+216], rax
	xor eax, eax
	mov QWORD PTR [rsp+224], rax
	xor eax, eax
	mov QWORD PTR [rsp+232], rax
	xor eax, eax
	mov QWORD PTR [rsp+240], rax
	xor eax, eax
	mov QWORD PTR [rsp+248], rax
	xor eax, eax
	mov QWORD PTR [rsp+256], rax
	xor eax, eax
	mov QWORD PTR [rsp+264], rax
	xor eax, eax
	mov QWORD PTR [rsp+272], rax
	xor eax, eax
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rsp+228], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsp+236], rax
	mov rax, QWORD PTR [rsi+12]
	mov QWORD PTR [rsp+240], rax
	movabs rax, 72340172838076673
	xor ecx, ecx
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+56], rcx
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+76]
	mov QWORD PTR [rdi+2268], rax
	mov eax, 0
	mov BYTE PTR [rdi+2276], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2277], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2285], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2293], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2301], rax
	mov rax, QWORD PTR [rsp+216]
	mov QWORD PTR [rdi+2309], rax
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rdi+2317], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi+2325], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rdi+2333], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 85
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 149
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 20
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 84
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1932]
	mov QWORD PTR [rsp+12], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 20
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 84
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 20
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 84
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1932]
	mov QWORD PTR [rsp+76], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+76]
	mov QWORD PTR [rdi+2268], rax
	mov eax, 1
	mov BYTE PTR [rdi+2276], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2277], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2285], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2293], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2301], rax
	mov rax, QWORD PTR [rsp+216]
	mov QWORD PTR [rdi+2309], rax
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rdi+2317], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi+2325], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rdi+2333], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 85
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 149
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 20
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 84
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1932]
	mov QWORD PTR [rsp+12], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 20
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 84
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 20
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 84
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1932]
	mov QWORD PTR [rsp+76], rax
	mov eax, 128
	mov QWORD PTR [rsp+176], rax
232:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 20
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 84
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 20
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 84
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1932]
	mov QWORD PTR [rsp+76], rax
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+360], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+368], rax
	mov rax, QWORD PTR [rsp+76]
	mov QWORD PTR [rsp+372], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 20
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 84
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 20
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 84
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1932]
	mov QWORD PTR [rsp+76], rax
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+380], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+388], rax
	mov rax, QWORD PTR [rsp+76]
	mov QWORD PTR [rsp+392], rax
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, rsp
	add rdx, 216
	mov rcx, rsp
	add rcx, 360
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_brainpoolp256r1_sign_k}
	mov rcx, QWORD PTR [rsp+176]
	sub rcx, 1
	mov QWORD PTR [rsp+176], rcx
	cmp eax, 1
	sbb rdx, rdx
	and rdx, rcx
	test rdx, rdx
	jne 233f
	xor edx, edx
	jmp 234f
233:
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+76]
	mov QWORD PTR [rdi+2268], rax
	mov eax, 0
	mov BYTE PTR [rdi+2276], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 21
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 85
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 20
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 84
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rdi+1932]
	mov QWORD PTR [rsp+12], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov eax, DWORD PTR [rsp+16]
	xor eax, ecx
	mov DWORD PTR [rdi+1808], eax
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 20
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 84
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 20
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 84
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rdi+1932]
	mov QWORD PTR [rsp+76], rax
	mov edx, 1
	test rdx, rdx
234:
	jne 232b
	xor ecx, ecx
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], rcx
	mov QWORD PTR [rsp+80], rcx
	mov QWORD PTR [rsp+88], rcx
	mov QWORD PTR [rsp+96], rcx
	mov QWORD PTR [rsp+104], rcx
	mov QWORD PTR [rsp+112], rcx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+144], rcx
	mov QWORD PTR [rsp+152], rcx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+168], rcx
	mov QWORD PTR [rsp+216], rcx
	mov QWORD PTR [rsp+224], rcx
	mov QWORD PTR [rsp+232], rcx
	mov QWORD PTR [rsp+240], rcx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rcx
	mov QWORD PTR [rsp+264], rcx
	mov QWORD PTR [rsp+272], rcx
	mov QWORD PTR [rsp+280], rcx
	mov QWORD PTR [rsp+288], rcx
	mov QWORD PTR [rsp+296], rcx
	mov QWORD PTR [rsp+304], rcx
	mov QWORD PTR [rsp+312], rcx
	mov QWORD PTR [rsp+320], rcx
	mov QWORD PTR [rsp+328], rcx
	mov QWORD PTR [rsp+336], rcx
	mov QWORD PTR [rsp+344], rcx
	mov QWORD PTR [rsp+352], rcx
	mov QWORD PTR [rsp+360], rcx
	mov QWORD PTR [rsp+368], rcx
	mov QWORD PTR [rsp+376], rcx
	mov QWORD PTR [rsp+384], rcx
	mov QWORD PTR [rsp+392], rcx
	mov QWORD PTR [rsp+400], rcx
	mov QWORD PTR [rsp+408], rcx
	mov QWORD PTR [rsp+416], rcx
	mov QWORD PTR [rsp+424], rcx
	mov QWORD PTR [rsp+432], rcx
	mov QWORD PTR [rsp+440], rcx
	mov QWORD PTR [rsp+448], rcx
	mov QWORD PTR [rsp+456], rcx
	mov QWORD PTR [rsp+464], rcx
	mov QWORD PTR [rsp+472], rcx
	mov QWORD PTR [rsp+480], rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
23:
	jmp 21f
20:
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rdi
	push rsi
	push rdx
	push rcx
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rsi, QWORD PTR [rsp+192]
	mov rdi, QWORD PTR [rsp+184]
	xor eax, eax
	mov QWORD PTR [rsp+216], rax
	xor eax, eax
	mov QWORD PTR [rsp+224], rax
	xor eax, eax
	mov QWORD PTR [rsp+232], rax
	xor eax, eax
	mov QWORD PTR [rsp+240], rax
	xor eax, eax
	mov QWORD PTR [rsp+248], rax
	xor eax, eax
	mov QWORD PTR [rsp+256], rax
	xor eax, eax
	mov QWORD PTR [rsp+264], rax
	xor eax, eax
	mov QWORD PTR [rsp+272], rax
	xor eax, eax
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsp+240], rax
	movabs rax, 72340172838076673
	xor ecx, ecx
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+56], rcx
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov eax, 0
	mov BYTE PTR [rdi+2272], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2273], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2281], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2289], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2297], rax
	mov rax, QWORD PTR [rsp+216]
	mov QWORD PTR [rdi+2305], rax
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rdi+2313], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rdi+2329], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov DWORD PTR [rdi+1808], ecx
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov DWORD PTR [rdi+1808], ecx
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 81
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 145
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 16
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 80
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov DWORD PTR [rdi+1808], ecx
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov DWORD PTR [rdi+1808], ecx
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 16
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 80
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 16
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 80
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov eax, 1
	mov BYTE PTR [rdi+2272], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2273], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2281], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2289], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2297], rax
	mov rax, QWORD PTR [rsp+216]
	mov QWORD PTR [rdi+2305], rax
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rdi+2313], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rdi+2329], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 81
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 145
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 16
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 80
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov DWORD PTR [rdi+1808], ecx
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov DWORD PTR [rdi+1808], ecx
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 16
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 80
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 16
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 80
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov eax, 128
	mov QWORD PTR [rsp+176], rax
235:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 16
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 80
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 16
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 80
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+360], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+368], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 16
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 80
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 16
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 80
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+376], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+384], rax
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, rsp
	add rdx, 216
	mov rcx, rsp
	add rcx, 360
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_brainpoolp256r1_sign_k}
	mov rcx, QWORD PTR [rsp+176]
	sub rcx, 1
	mov QWORD PTR [rsp+176], rcx
	cmp eax, 1
	sbb rdx, rdx
	and rdx, rcx
	test rdx, rdx
	jne 236f
	xor edx, edx
	jmp 237f
236:
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov eax, 0
	mov BYTE PTR [rdi+2272], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov DWORD PTR [rdi+1808], ecx
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov DWORD PTR [rdi+1808], ecx
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 17
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 81
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 16
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 80
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+8], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 909522486
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov DWORD PTR [rdi+1808], ecx
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov ecx, 1549556828
	mov eax, DWORD PTR [rsp]
	xor eax, ecx
	mov DWORD PTR [rdi+1792], eax
	mov eax, DWORD PTR [rsp+4]
	xor eax, ecx
	mov DWORD PTR [rdi+1796], eax
	mov eax, DWORD PTR [rsp+8]
	xor eax, ecx
	mov DWORD PTR [rdi+1800], eax
	mov eax, DWORD PTR [rsp+12]
	xor eax, ecx
	mov DWORD PTR [rdi+1804], eax
	mov DWORD PTR [rdi+1808], ecx
	mov DWORD PTR [rdi+1812], ecx
	mov DWORD PTR [rdi+1816], ecx
	mov DWORD PTR [rdi+1820], ecx
	mov DWORD PTR [rdi+1824], ecx
	mov DWORD PTR [rdi+1828], ecx
	mov DWORD PTR [rdi+1832], ecx
	mov DWORD PTR [rdi+1836], ecx
	mov DWORD PTR [rdi+1840], ecx
	mov DWORD PTR [rdi+1844], ecx
	mov DWORD PTR [rdi+1848], ecx
	mov DWORD PTR [rdi+1852], ecx
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1792
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 16
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 80
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov ecx, 16
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 192
	mov esi, 80
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1920
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 384
	mov r11, QWORD PTR [rsp+488]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rsp+72], rax
	mov edx, 1
	test rdx, rdx
237:
	jne 235b
	xor ecx, ecx
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], rcx
	mov QWORD PTR [rsp+80], rcx
	mov QWORD PTR [rsp+88], rcx
	mov QWORD PTR [rsp+96], rcx
	mov QWORD PTR [rsp+104], rcx
	mov QWORD PTR [rsp+112], rcx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+144], rcx
	mov QWORD PTR [rsp+152], rcx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+168], rcx
	mov QWORD PTR [rsp+216], rcx
	mov QWORD PTR [rsp+224], rcx
	mov QWORD PTR [rsp+232], rcx
	mov QWORD PTR [rsp+240], rcx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rcx
	mov QWORD PTR [rsp+264], rcx
	mov QWORD PTR [rsp+272], rcx
	mov QWORD PTR [rsp+280], rcx
	mov QWORD PTR [rsp+288], rcx
	mov QWORD PTR [rsp+296], rcx
	mov QWORD PTR [rsp+304], rcx
	mov QWORD PTR [rsp+312], rcx
	mov QWORD PTR [rsp+320], rcx
	mov QWORD PTR [rsp+328], rcx
	mov QWORD PTR [rsp+336], rcx
	mov QWORD PTR [rsp+344], rcx
	mov QWORD PTR [rsp+352], rcx
	mov QWORD PTR [rsp+360], rcx
	mov QWORD PTR [rsp+368], rcx
	mov QWORD PTR [rsp+376], rcx
	mov QWORD PTR [rsp+384], rcx
	mov QWORD PTR [rsp+392], rcx
	mov QWORD PTR [rsp+400], rcx
	mov QWORD PTR [rsp+408], rcx
	mov QWORD PTR [rsp+416], rcx
	mov QWORD PTR [rsp+424], rcx
	mov QWORD PTR [rsp+432], rcx
	mov QWORD PTR [rsp+440], rcx
	mov QWORD PTR [rsp+448], rcx
	mov QWORD PTR [rsp+456], rcx
	mov QWORD PTR [rsp+464], rcx
	mov QWORD PTR [rsp+472], rcx
	mov QWORD PTR [rsp+480], rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
21:
	ret
	.p2align 6
