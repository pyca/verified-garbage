// The functions of `src/ecdh_brainpoolp320r1.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdh_brainpoolp320r1:
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
	mov rax, QWORD PTR [rcx+32]
	bswap rax
	mov QWORD PTR [rdi+1304], rax
	mov rax, QWORD PTR [rcx+24]
	bswap rax
	mov QWORD PTR [rdi+1312], rax
	mov rax, QWORD PTR [rcx+16]
	bswap rax
	mov QWORD PTR [rdi+1320], rax
	mov rax, QWORD PTR [rcx+8]
	bswap rax
	mov QWORD PTR [rdi+1328], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	mov QWORD PTR [rdi+1336], rax
	mov rax, QWORD PTR [rsi+32]
	bswap rax
	mov QWORD PTR [rdi+1344], rax
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rdi+1352], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdx+32]
	bswap rax
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1416], rax
	movabs rax, -228537125615489497
	mov QWORD PTR [rdi+64], rax
	movabs rax, 5733849700882443304
	mov QWORD PTR [rdi+72], rax
	movabs rax, -463923920581161489
	mov QWORD PTR [rdi+80], rax
	movabs rax, -2216764567927529371
	mov QWORD PTR [rdi+88], rax
	movabs rax, -3216054880213119049
	mov QWORD PTR [rdi+96], rax
	movabs rax, -8750118750519979247
	mov QWORD PTR [rdi+104], rax
	movabs rax, 3262909366265075945
	mov QWORD PTR [rdi+112], rax
	movabs rax, -463923925956488541
	mov QWORD PTR [rdi+120], rax
	movabs rax, -2216764567927529371
	mov QWORD PTR [rdi+128], rax
	movabs rax, -3216054880213119049
	mov QWORD PTR [rdi+136], rax
	movabs rax, 0
	mov QWORD PTR [rdi+184], rax
	movabs rax, 0
	mov QWORD PTR [rdi+192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+216], rax
	movabs rax, 1
	mov QWORD PTR [rdi+224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+248], rax
	movabs rax, 0
	mov QWORD PTR [rdi+256], rax
	movabs rax, 228537125615489497
	mov QWORD PTR [rdi+264], rax
	movabs rax, -5733849700882443305
	mov QWORD PTR [rdi+272], rax
	movabs rax, 463923920581161488
	mov QWORD PTR [rdi+280], rax
	movabs rax, 2216764567927529370
	mov QWORD PTR [rdi+288], rax
	movabs rax, 3216054880213119048
	mov QWORD PTR [rdi+296], rax
	movabs rax, 2356493640398878114
	mov QWORD PTR [rdi+304], rax
	movabs rax, 284969695562620806
	mov QWORD PTR [rdi+312], rax
	movabs rax, -6829247170020331501
	mov QWORD PTR [rdi+320], rax
	movabs rax, 4194426753620063967
	mov QWORD PTR [rdi+328], rax
	movabs rax, 5078856112967687526
	mov QWORD PTR [rdi+336], rax
	movabs rax, 7053452331654788352
	mov QWORD PTR [rdi+344], rax
	movabs rax, -6986561034376603457
	mov QWORD PTR [rdi+352], rax
	movabs rax, 6189360142709985548
	mov QWORD PTR [rdi+360], rax
	movabs rax, -1011369721526533541
	mov QWORD PTR [rdi+368], rax
	movabs rax, 1362199378405645001
	mov QWORD PTR [rdi+376], rax
	movabs rax, -4786659617243657543
	mov QWORD PTR [rdi+384], rax
	movabs rax, -1265231511225044741
	mov QWORD PTR [rdi+392], rax
	movabs rax, 8082549764844786590
	mov QWORD PTR [rdi+400], rax
	movabs rax, 6219451310284087795
	mov QWORD PTR [rdi+408], rax
	movabs rax, 4931152090802418916
	mov QWORD PTR [rdi+416], rax
	movabs rax, 6053180428327346508
	mov QWORD PTR [rdi+424], rax
	movabs rax, -4143445765385166215
	mov QWORD PTR [rdi+432], rax
	movabs rax, 6058259963329842167
	mov QWORD PTR [rdi+440], rax
	movabs rax, -330422891442749831
	mov QWORD PTR [rdi+448], rax
	movabs rax, 8546305432622508938
	mov QWORD PTR [rdi+456], rax
	movabs rax, 7466169795626656973
	mov QWORD PTR [rdi+464], rax
	movabs rax, -7943505198014437371
	mov QWORD PTR [rdi+472], rax
	movabs rax, -8740588864839171063
	mov QWORD PTR [rdi+480], rax
	movabs rax, -2085952622352428802
	mov QWORD PTR [rdi+488], rax
	movabs rax, 3597399491969331535
	mov QWORD PTR [rdi+496], rax
	movabs rax, 8750118750519979247
	mov QWORD PTR [rdi+504], rax
	movabs rax, -3262909366265075946
	mov QWORD PTR [rdi+512], rax
	movabs rax, 463923925956488540
	mov QWORD PTR [rdi+520], rax
	movabs rax, 2216764567927529370
	mov QWORD PTR [rdi+528], rax
	movabs rax, 3216054880213119048
	mov QWORD PTR [rdi+536], rax
	movabs rax, -228537125615489499
	mov QWORD PTR [rdi+544], rax
	movabs rax, 5733849700882443304
	mov QWORD PTR [rdi+552], rax
	movabs rax, -463923920581161489
	mov QWORD PTR [rdi+560], rax
	movabs rax, -2216764567927529371
	mov QWORD PTR [rdi+568], rax
	movabs rax, -3216054880213119049
	mov QWORD PTR [rdi+576], rax
	movabs rax, -8750118750519979249
	mov QWORD PTR [rdi+584], rax
	movabs rax, 3262909366265075945
	mov QWORD PTR [rdi+592], rax
	movabs rax, -463923925956488541
	mov QWORD PTR [rdi+600], rax
	movabs rax, -2216764567927529371
	mov QWORD PTR [rdi+608], rax
	movabs rax, -3216054880213119049
	mov QWORD PTR [rdi+616], rax
	movabs rax, 0
	mov QWORD PTR [rdi+624], rax
	movabs rax, 0
	mov QWORD PTR [rdi+632], rax
	movabs rax, 0
	mov QWORD PTR [rdi+640], rax
	movabs rax, 0
	mov QWORD PTR [rdi+648], rax
	movabs rax, 0
	mov QWORD PTR [rdi+656], rax
	movabs rax, 228537125615489497
	mov QWORD PTR [rdi+664], rax
	movabs rax, -5733849700882443305
	mov QWORD PTR [rdi+672], rax
	movabs rax, 463923920581161488
	mov QWORD PTR [rdi+680], rax
	movabs rax, 2216764567927529370
	mov QWORD PTR [rdi+688], rax
	movabs rax, 3216054880213119048
	mov QWORD PTR [rdi+696], rax
	movabs rax, 0
	mov QWORD PTR [rdi+704], rax
	movabs rax, 0
	mov QWORD PTR [rdi+712], rax
	movabs rax, 0
	mov QWORD PTR [rdi+720], rax
	movabs rax, 0
	mov QWORD PTR [rdi+728], rax
	movabs rax, 0
	mov QWORD PTR [rdi+736], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1824], rax
	mov rsi, r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+1304]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1864], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1865], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1866], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1867], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1868], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1869], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1870], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1871], dl
	add rbx, 1
	cmp rbx, 40
	jne 20b
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rdi+rbx*1+544]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2192], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2193], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2194], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2195], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2196], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2197], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2198], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2199], dl
	add rbx, 1
	cmp rbx, 40
	jne 21b
	mov ebx, 0
22:
	movzx eax, BYTE PTR [rdi+rbx*1+584]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2520], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2521], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2522], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2523], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2524], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2525], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2526], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2527], dl
	add rbx, 1
	cmp rbx, 40
	jne 22b
	movabs rax, -7399721456369970439
	mov QWORD PTR [rdi+1624], rax
	movabs rax, -4447433766387222289
	mov QWORD PTR [rdi+1632], rax
	movabs rax, 2255327180949403254
	mov QWORD PTR [rdi+1640], rax
	movabs rax, 6076949523028301522
	mov QWORD PTR [rdi+1648], rax
	movabs rax, -6748157737832705454
	mov QWORD PTR [rdi+1656], rax
	movabs rax, -3950121997761914086
	mov QWORD PTR [rdi+1664], rax
	movabs rax, 1493712789129427717
	mov QWORD PTR [rdi+1672], rax
	movabs rax, 1753837433849220857
	mov QWORD PTR [rdi+1680], rax
	movabs rax, -7963880977030381299
	mov QWORD PTR [rdi+1688], rax
	movabs rax, -7838884818576714904
	mov QWORD PTR [rdi+1696], rax
	mov rdx, r9
	add rdx, 41
	mov rax, QWORD PTR [rdx+32]
	bswap rax
	mov QWORD PTR [rdi+1504], rax
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1512], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1520], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1528], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1536], rax
	movzx edx, BYTE PTR [r9]
	xor rdx, 4
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1824]
	and rax, rdx
	mov QWORD PTR [rdi+1824], rax
	call {vg_brainpoolp320r1_check_point}
	mov rax, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rdi+1792]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rdi+1800]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rdi+1808]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rdi+1816]
	mov QWORD PTR [rdi+696], rax
	call {vg_brainpoolp320r1_mul}
	call {vg_brainpoolp320r1_inv_mod_p}
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+624]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
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
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+632]
	mov ebp, 0
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
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
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
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+640]
	mov ebp, 0
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+648]
	mov ebp, 0
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+656]
	mov ebp, 0
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
	movabs rcx, 4404128606415658601
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
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1424], r13
	mov QWORD PTR [rdi+1432], r14
	mov QWORD PTR [rdi+1440], r8
	mov QWORD PTR [rdi+1448], r9
	mov QWORD PTR [rdi+1456], r10
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
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
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
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
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
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
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1456]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
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
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1464], r13
	mov QWORD PTR [rdi+1472], r14
	mov QWORD PTR [rdi+1480], r8
	mov QWORD PTR [rdi+1488], r9
	mov QWORD PTR [rdi+1496], r10
	mov rdx, QWORD PTR [rdi+1344]
	sub rdx, QWORD PTR [rdi+104]
	mov rdx, QWORD PTR [rdi+1352]
	sbb rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1360]
	sbb rdx, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+1368]
	sbb rdx, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rdi+1376]
	sbb rdx, QWORD PTR [rdi+136]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+1344]
	or rdx, QWORD PTR [rdi+1352]
	or rdx, QWORD PTR [rdi+1360]
	or rdx, QWORD PTR [rdi+1368]
	or rdx, QWORD PTR [rdi+1376]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+1824]
	and rax, rdx
	mov QWORD PTR [rdi+1824], rax
	mov rdx, QWORD PTR [rdi+704]
	or rdx, QWORD PTR [rdi+712]
	or rdx, QWORD PTR [rdi+720]
	or rdx, QWORD PTR [rdi+728]
	or rdx, QWORD PTR [rdi+736]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1824]
	and rax, rdx
	mov QWORD PTR [rdi+1824], rax
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1464]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+32], rax
	mov rax, QWORD PTR [rdi+1472]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+24], rax
	mov rax, QWORD PTR [rdi+1480]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rdi+1488]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rdi+1496]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi], rax
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
	lea rsp, [rsp-8]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6
