// The functions of `src/ec_p224_validate.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p224_validate_public_key:
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
	mov rax, QWORD PTR [rcx+20]
	bswap rax
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rcx+12]
	bswap rax
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rcx+4]
	bswap rax
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	shr rax, 32
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rsi+20]
	bswap rax
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rsi+12]
	bswap rax
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rsi+4]
	bswap rax
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 32
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdx+20]
	bswap rax
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdx+12]
	bswap rax
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdx+4]
	bswap rax
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	shr rax, 32
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 1
	mov QWORD PTR [rdi+64], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+72], rax
	movabs rax, -1
	mov QWORD PTR [rdi+80], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+88], rax
	movabs rax, 1431345634452711997
	mov QWORD PTR [rdi+96], rax
	movabs rax, -256586165981122
	mov QWORD PTR [rdi+104], rax
	movabs rax, -1
	mov QWORD PTR [rdi+112], rax
	movabs rax, 4294967295
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
	movabs rax, -4294967296
	mov QWORD PTR [rdi+224], rax
	movabs rax, -1
	mov QWORD PTR [rdi+232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+248], rax
	movabs rax, 12884901889
	mov QWORD PTR [rdi+256], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+264], rax
	movabs rax, -4
	mov QWORD PTR [rdi+272], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+280], rax
	movabs rax, -5315819985753272986
	mov QWORD PTR [rdi+288], rax
	movabs rax, 3562427416704989490
	mov QWORD PTR [rdi+296], rax
	movabs rax, -5085637333085617165
	mov QWORD PTR [rdi+304], rax
	movabs rax, 2134937273
	mov QWORD PTR [rdi+312], rax
	movabs rax, -4859293672941139222
	mov QWORD PTR [rdi+320], rax
	movabs rax, -8852503232730579030
	mov QWORD PTR [rdi+328], rax
	movabs rax, 7913862054659484677
	mov QWORD PTR [rdi+336], rax
	movabs rax, 2719702624
	mov QWORD PTR [rdi+344], rax
	movabs rax, 3376751829566352872
	mov QWORD PTR [rdi+352], rax
	movabs rax, -518644947609232789
	mov QWORD PTR [rdi+360], rax
	movabs rax, -5860936088866002824
	mov QWORD PTR [rdi+368], rax
	movabs rax, 1632077553
	mov QWORD PTR [rdi+376], rax
	movabs rax, 2996154245097553173
	mov QWORD PTR [rdi+384], rax
	movabs rax, -6068319739328446645
	mov QWORD PTR [rdi+392], rax
	movabs rax, 7697038227981551702
	mov QWORD PTR [rdi+400], rax
	movabs rax, 2984868193
	mov QWORD PTR [rdi+408], rax
	movabs rax, -6655240790828122112
	mov QWORD PTR [rdi+416], rax
	movabs rax, 2253787464087033530
	mov QWORD PTR [rdi+424], rax
	movabs rax, 59741
	mov QWORD PTR [rdi+432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+440], rax
	movabs rax, -1
	mov QWORD PTR [rdi+448], rax
	movabs rax, -4294967297
	mov QWORD PTR [rdi+456], rax
	movabs rax, -1
	mov QWORD PTR [rdi+464], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+472], rax
	movabs rax, 1431345634452711995
	mov QWORD PTR [rdi+480], rax
	movabs rax, -256586165981122
	mov QWORD PTR [rdi+488], rax
	movabs rax, -1
	mov QWORD PTR [rdi+496], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+504], rax
	movabs rax, 0
	mov QWORD PTR [rdi+512], rax
	movabs rax, 0
	mov QWORD PTR [rdi+520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+536], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+544], rax
	movabs rax, -1
	mov QWORD PTR [rdi+552], rax
	movabs rax, 0
	mov QWORD PTR [rdi+560], rax
	movabs rax, 0
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
	movabs rax, -4294967295
	mov QWORD PTR [rdi+1312], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+1320], rax
	movabs rax, -8589934592
	mov QWORD PTR [rdi+1328], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+1336], rax
	movabs rax, -1771939995251090995
	mov QWORD PTR [rdi+1344], rax
	movabs rax, 1187475804136674064
	mov QWORD PTR [rdi+1352], rax
	movabs rax, 4453702246874644817
	mov QWORD PTR [rdi+1360], rax
	movabs rax, 2143301523
	mov QWORD PTR [rdi+1368], rax
	mov rdx, r9
	add rdx, 29
	mov rax, QWORD PTR [rdx+20]
	bswap rax
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdx+12]
	bswap rax
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdx+4]
	bswap rax
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	shr rax, 32
	mov QWORD PTR [rdi+1240], rax
	movzx edx, BYTE PTR [r9]
	xor rdx, 4
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	call {vg_p224_check_point}
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
