// The functions of `src/ec_brainpoolp256r1_validate.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp256r1_validate_public_key:
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
	mov rcx, QWORD PTR [rdi+1472]
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
