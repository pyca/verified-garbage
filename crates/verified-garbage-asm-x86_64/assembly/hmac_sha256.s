// The functions of `src/hmac_sha256.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha256_init:
	cmp rcx, 65
	jae 20f
	lea rsp, [rsp-840]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+608], rbx
	mov QWORD PTR [r8+616], rbp
	mov QWORD PTR [r8+624], r12
	mov QWORD PTR [r8+632], r13
	mov QWORD PTR [r8+640], r14
	mov QWORD PTR [r8+648], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha256_init}
	mov rdi, r12
	call {vg_sha256_init}
	mov eax, 909522486
	mov DWORD PTR [rbx+32], eax
	mov DWORD PTR [rbx+36], eax
	mov DWORD PTR [rbx+40], eax
	mov DWORD PTR [rbx+44], eax
	mov DWORD PTR [rbx+48], eax
	mov DWORD PTR [rbx+52], eax
	mov DWORD PTR [rbx+56], eax
	mov DWORD PTR [rbx+60], eax
	mov DWORD PTR [rbx+64], eax
	mov DWORD PTR [rbx+68], eax
	mov DWORD PTR [rbx+72], eax
	mov DWORD PTR [rbx+76], eax
	mov DWORD PTR [rbx+80], eax
	mov DWORD PTR [rbx+84], eax
	mov DWORD PTR [rbx+88], eax
	mov DWORD PTR [rbx+92], eax
	mov r14d, 0
	test r13, r13
	je 22f
24:
	movzx eax, BYTE PTR [rbp+r14*1]
	xor eax, 54
	mov BYTE PTR [rbx+r14*1+32], al
	add r14, 1
	cmp r14, r13
	jne 24b
	jmp 23f
22:
23:
	mov eax, DWORD PTR [rbx+32]
	xor eax, 1785358954
	mov DWORD PTR [r12+32], eax
	mov eax, DWORD PTR [rbx+36]
	xor eax, 1785358954
	mov DWORD PTR [r12+36], eax
	mov eax, DWORD PTR [rbx+40]
	xor eax, 1785358954
	mov DWORD PTR [r12+40], eax
	mov eax, DWORD PTR [rbx+44]
	xor eax, 1785358954
	mov DWORD PTR [r12+44], eax
	mov eax, DWORD PTR [rbx+48]
	xor eax, 1785358954
	mov DWORD PTR [r12+48], eax
	mov eax, DWORD PTR [rbx+52]
	xor eax, 1785358954
	mov DWORD PTR [r12+52], eax
	mov eax, DWORD PTR [rbx+56]
	xor eax, 1785358954
	mov DWORD PTR [r12+56], eax
	mov eax, DWORD PTR [rbx+60]
	xor eax, 1785358954
	mov DWORD PTR [r12+60], eax
	mov eax, DWORD PTR [rbx+64]
	xor eax, 1785358954
	mov DWORD PTR [r12+64], eax
	mov eax, DWORD PTR [rbx+68]
	xor eax, 1785358954
	mov DWORD PTR [r12+68], eax
	mov eax, DWORD PTR [rbx+72]
	xor eax, 1785358954
	mov DWORD PTR [r12+72], eax
	mov eax, DWORD PTR [rbx+76]
	xor eax, 1785358954
	mov DWORD PTR [r12+76], eax
	mov eax, DWORD PTR [rbx+80]
	xor eax, 1785358954
	mov DWORD PTR [r12+80], eax
	mov eax, DWORD PTR [rbx+84]
	xor eax, 1785358954
	mov DWORD PTR [r12+84], eax
	mov eax, DWORD PTR [rbx+88]
	xor eax, 1785358954
	mov DWORD PTR [r12+88], eax
	mov eax, DWORD PTR [rbx+92]
	xor eax, 1785358954
	mov DWORD PTR [r12+92], eax
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+608]
	mov rbp, QWORD PTR [r15+616]
	mov r12, QWORD PTR [r15+624]
	mov r13, QWORD PTR [r15+632]
	mov r14, QWORD PTR [r15+640]
	mov r15, QWORD PTR [r15+648]
	lea rsp, [rsp+840]
21:
	ret
20:
	lea rsp, [rsp-1608]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+832], rbx
	mov QWORD PTR [r8+840], rbp
	mov QWORD PTR [r8+848], r12
	mov QWORD PTR [r8+856], r13
	mov QWORD PTR [r8+864], r14
	mov QWORD PTR [r8+872], r15
	mov r15, r8
	mov rbx, rdx
	mov rbp, rcx
	mov r12, rdi
	mov r13, rsi
	cmp rbp, 65
	jae 25f
	mov rdx, rbx
	mov rcx, rbp
	jmp 26f
25:
	mov rdi, r15
	add rdi, 1184
	call {vg_sha256_init}
	mov rdi, r15
	add rdi, 1184
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha256_update_scratch}
	mov rdi, r15
	add rdi, 1184
	mov rsi, rbp
	mov rdx, r15
	add rdx, 1344
	mov rcx, r15
	call {vg_sha256_finalize_scratch}
	mov rdx, r15
	add rdx, 1344
	mov ecx, 32
26:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha256_init_scratch}
	mov rbx, QWORD PTR [r15+832]
	mov rbp, QWORD PTR [r15+840]
	mov r12, QWORD PTR [r15+848]
	mov r13, QWORD PTR [r15+856]
	mov r14, QWORD PTR [r15+864]
	mov r15, QWORD PTR [r15+872]
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	mov QWORD PTR [rsp+1032], r11
	mov QWORD PTR [rsp+1040], r11
	mov QWORD PTR [rsp+1048], r11
	mov QWORD PTR [rsp+1056], r11
	mov QWORD PTR [rsp+1064], r11
	mov QWORD PTR [rsp+1072], r11
	mov QWORD PTR [rsp+1080], r11
	mov QWORD PTR [rsp+1088], r11
	mov QWORD PTR [rsp+1096], r11
	mov QWORD PTR [rsp+1104], r11
	mov QWORD PTR [rsp+1112], r11
	mov QWORD PTR [rsp+1120], r11
	mov QWORD PTR [rsp+1128], r11
	mov QWORD PTR [rsp+1136], r11
	mov QWORD PTR [rsp+1144], r11
	mov QWORD PTR [rsp+1152], r11
	mov QWORD PTR [rsp+1160], r11
	mov QWORD PTR [rsp+1168], r11
	mov QWORD PTR [rsp+1176], r11
	mov QWORD PTR [rsp+1184], r11
	mov QWORD PTR [rsp+1192], r11
	mov QWORD PTR [rsp+1200], r11
	mov QWORD PTR [rsp+1208], r11
	mov QWORD PTR [rsp+1216], r11
	mov QWORD PTR [rsp+1224], r11
	mov QWORD PTR [rsp+1232], r11
	mov QWORD PTR [rsp+1240], r11
	mov QWORD PTR [rsp+1248], r11
	mov QWORD PTR [rsp+1256], r11
	mov QWORD PTR [rsp+1264], r11
	mov QWORD PTR [rsp+1272], r11
	mov QWORD PTR [rsp+1280], r11
	mov QWORD PTR [rsp+1288], r11
	mov QWORD PTR [rsp+1296], r11
	mov QWORD PTR [rsp+1304], r11
	mov QWORD PTR [rsp+1312], r11
	mov QWORD PTR [rsp+1320], r11
	mov QWORD PTR [rsp+1328], r11
	mov QWORD PTR [rsp+1336], r11
	mov QWORD PTR [rsp+1344], r11
	mov QWORD PTR [rsp+1352], r11
	mov QWORD PTR [rsp+1360], r11
	mov QWORD PTR [rsp+1368], r11
	mov QWORD PTR [rsp+1376], r11
	mov QWORD PTR [rsp+1384], r11
	mov QWORD PTR [rsp+1392], r11
	mov QWORD PTR [rsp+1400], r11
	mov QWORD PTR [rsp+1408], r11
	mov QWORD PTR [rsp+1416], r11
	mov QWORD PTR [rsp+1424], r11
	mov QWORD PTR [rsp+1432], r11
	mov QWORD PTR [rsp+1440], r11
	mov QWORD PTR [rsp+1448], r11
	mov QWORD PTR [rsp+1456], r11
	mov QWORD PTR [rsp+1464], r11
	mov QWORD PTR [rsp+1472], r11
	mov QWORD PTR [rsp+1480], r11
	mov QWORD PTR [rsp+1488], r11
	mov QWORD PTR [rsp+1496], r11
	mov QWORD PTR [rsp+1504], r11
	mov QWORD PTR [rsp+1512], r11
	mov QWORD PTR [rsp+1520], r11
	mov QWORD PTR [rsp+1528], r11
	mov QWORD PTR [rsp+1536], r11
	mov QWORD PTR [rsp+1544], r11
	mov QWORD PTR [rsp+1552], r11
	mov QWORD PTR [rsp+1560], r11
	mov QWORD PTR [rsp+1568], r11
	mov QWORD PTR [rsp+1576], r11
	mov QWORD PTR [rsp+1584], r11
	mov QWORD PTR [rsp+1592], r11
	mov QWORD PTR [rsp+1600], r11
	lea rsp, [rsp+1608]
	jmp 21b
	.p2align 6

vg_hmac_sha256_finalize:
	lea rsp, [rsp-840]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+608], rbx
	mov QWORD PTR [r8+616], rbp
	mov QWORD PTR [r8+624], r12
	mov QWORD PTR [r8+632], r13
	mov QWORD PTR [r8+640], r14
	mov QWORD PTR [r8+648], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 656
	mov rcx, r15
	call {vg_sha256_finalize_scratch}
	mov eax, DWORD PTR [r12]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+4]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+8]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+12]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+16]
	mov DWORD PTR [rbx+16], eax
	mov eax, DWORD PTR [r12+20]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+24]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+28]
	mov DWORD PTR [rbx+28], eax
	mov eax, DWORD PTR [r15+656]
	mov DWORD PTR [rbx+32], eax
	mov eax, DWORD PTR [r15+660]
	mov DWORD PTR [rbx+36], eax
	mov eax, DWORD PTR [r15+664]
	mov DWORD PTR [rbx+40], eax
	mov eax, DWORD PTR [r15+668]
	mov DWORD PTR [rbx+44], eax
	mov eax, DWORD PTR [r15+672]
	mov DWORD PTR [rbx+48], eax
	mov eax, DWORD PTR [r15+676]
	mov DWORD PTR [rbx+52], eax
	mov eax, DWORD PTR [r15+680]
	mov DWORD PTR [rbx+56], eax
	mov eax, DWORD PTR [r15+684]
	mov DWORD PTR [rbx+60], eax
	mov rbp, rbx
	add rbp, 32
	mov eax, 128
	mov DWORD PTR [rbp+32], eax
	mov eax, 0
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 96
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbp, r13
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
	mov rbx, QWORD PTR [r15+608]
	mov rbp, QWORD PTR [r15+616]
	mov r12, QWORD PTR [r15+624]
	mov r13, QWORD PTR [r15+632]
	mov r14, QWORD PTR [r15+640]
	mov r15, QWORD PTR [r15+648]
	lea rsp, [rsp+840]
	ret
	.p2align 6

vg_hmac_sha256_init_scratch:
	mov QWORD PTR [r8+608], rbx
	mov QWORD PTR [r8+616], rbp
	mov QWORD PTR [r8+624], r12
	mov QWORD PTR [r8+632], r13
	mov QWORD PTR [r8+640], r14
	mov QWORD PTR [r8+648], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha256_init}
	mov rdi, r12
	call {vg_sha256_init}
	mov eax, 909522486
	mov DWORD PTR [rbx+32], eax
	mov DWORD PTR [rbx+36], eax
	mov DWORD PTR [rbx+40], eax
	mov DWORD PTR [rbx+44], eax
	mov DWORD PTR [rbx+48], eax
	mov DWORD PTR [rbx+52], eax
	mov DWORD PTR [rbx+56], eax
	mov DWORD PTR [rbx+60], eax
	mov DWORD PTR [rbx+64], eax
	mov DWORD PTR [rbx+68], eax
	mov DWORD PTR [rbx+72], eax
	mov DWORD PTR [rbx+76], eax
	mov DWORD PTR [rbx+80], eax
	mov DWORD PTR [rbx+84], eax
	mov DWORD PTR [rbx+88], eax
	mov DWORD PTR [rbx+92], eax
	mov r14d, 0
	test r13, r13
	je 20f
22:
	movzx eax, BYTE PTR [rbp+r14*1]
	xor eax, 54
	mov BYTE PTR [rbx+r14*1+32], al
	add r14, 1
	cmp r14, r13
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [rbx+32]
	xor eax, 1785358954
	mov DWORD PTR [r12+32], eax
	mov eax, DWORD PTR [rbx+36]
	xor eax, 1785358954
	mov DWORD PTR [r12+36], eax
	mov eax, DWORD PTR [rbx+40]
	xor eax, 1785358954
	mov DWORD PTR [r12+40], eax
	mov eax, DWORD PTR [rbx+44]
	xor eax, 1785358954
	mov DWORD PTR [r12+44], eax
	mov eax, DWORD PTR [rbx+48]
	xor eax, 1785358954
	mov DWORD PTR [r12+48], eax
	mov eax, DWORD PTR [rbx+52]
	xor eax, 1785358954
	mov DWORD PTR [r12+52], eax
	mov eax, DWORD PTR [rbx+56]
	xor eax, 1785358954
	mov DWORD PTR [r12+56], eax
	mov eax, DWORD PTR [rbx+60]
	xor eax, 1785358954
	mov DWORD PTR [r12+60], eax
	mov eax, DWORD PTR [rbx+64]
	xor eax, 1785358954
	mov DWORD PTR [r12+64], eax
	mov eax, DWORD PTR [rbx+68]
	xor eax, 1785358954
	mov DWORD PTR [r12+68], eax
	mov eax, DWORD PTR [rbx+72]
	xor eax, 1785358954
	mov DWORD PTR [r12+72], eax
	mov eax, DWORD PTR [rbx+76]
	xor eax, 1785358954
	mov DWORD PTR [r12+76], eax
	mov eax, DWORD PTR [rbx+80]
	xor eax, 1785358954
	mov DWORD PTR [r12+80], eax
	mov eax, DWORD PTR [rbx+84]
	xor eax, 1785358954
	mov DWORD PTR [r12+84], eax
	mov eax, DWORD PTR [rbx+88]
	xor eax, 1785358954
	mov DWORD PTR [r12+88], eax
	mov eax, DWORD PTR [rbx+92]
	xor eax, 1785358954
	mov DWORD PTR [r12+92], eax
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+608]
	mov rbp, QWORD PTR [r15+616]
	mov r12, QWORD PTR [r15+624]
	mov r13, QWORD PTR [r15+632]
	mov r14, QWORD PTR [r15+640]
	mov r15, QWORD PTR [r15+648]
	ret
	.p2align 6

vg_hmac_sha256_finalize_scratch:
	mov QWORD PTR [r8+608], rbx
	mov QWORD PTR [r8+616], rbp
	mov QWORD PTR [r8+624], r12
	mov QWORD PTR [r8+632], r13
	mov QWORD PTR [r8+640], r14
	mov QWORD PTR [r8+648], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 656
	mov rcx, r15
	call {vg_sha256_finalize_scratch}
	mov eax, DWORD PTR [r12]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+4]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+8]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+12]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+16]
	mov DWORD PTR [rbx+16], eax
	mov eax, DWORD PTR [r12+20]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+24]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+28]
	mov DWORD PTR [rbx+28], eax
	mov eax, DWORD PTR [r15+656]
	mov DWORD PTR [rbx+32], eax
	mov eax, DWORD PTR [r15+660]
	mov DWORD PTR [rbx+36], eax
	mov eax, DWORD PTR [r15+664]
	mov DWORD PTR [rbx+40], eax
	mov eax, DWORD PTR [r15+668]
	mov DWORD PTR [rbx+44], eax
	mov eax, DWORD PTR [r15+672]
	mov DWORD PTR [rbx+48], eax
	mov eax, DWORD PTR [r15+676]
	mov DWORD PTR [rbx+52], eax
	mov eax, DWORD PTR [r15+680]
	mov DWORD PTR [rbx+56], eax
	mov eax, DWORD PTR [r15+684]
	mov DWORD PTR [rbx+60], eax
	mov rbp, rbx
	add rbp, 32
	mov eax, 128
	mov DWORD PTR [rbp+32], eax
	mov eax, 0
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 96
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbp, r13
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
	mov rbx, QWORD PTR [r15+608]
	mov rbp, QWORD PTR [r15+616]
	mov r12, QWORD PTR [r15+624]
	mov r13, QWORD PTR [r15+632]
	mov r14, QWORD PTR [r15+640]
	mov r15, QWORD PTR [r15+648]
	ret
	.p2align 6

vg_hmac_sha256_init_avx2:
	cmp rcx, 65
	jae 20f
	lea rsp, [rsp-840]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+608], rbx
	mov QWORD PTR [r8+616], rbp
	mov QWORD PTR [r8+624], r12
	mov QWORD PTR [r8+632], r13
	mov QWORD PTR [r8+640], r14
	mov QWORD PTR [r8+648], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha256_init}
	mov rdi, r12
	call {vg_sha256_init}
	mov eax, 909522486
	mov DWORD PTR [rbx+32], eax
	mov DWORD PTR [rbx+36], eax
	mov DWORD PTR [rbx+40], eax
	mov DWORD PTR [rbx+44], eax
	mov DWORD PTR [rbx+48], eax
	mov DWORD PTR [rbx+52], eax
	mov DWORD PTR [rbx+56], eax
	mov DWORD PTR [rbx+60], eax
	mov DWORD PTR [rbx+64], eax
	mov DWORD PTR [rbx+68], eax
	mov DWORD PTR [rbx+72], eax
	mov DWORD PTR [rbx+76], eax
	mov DWORD PTR [rbx+80], eax
	mov DWORD PTR [rbx+84], eax
	mov DWORD PTR [rbx+88], eax
	mov DWORD PTR [rbx+92], eax
	mov r14d, 0
	test r13, r13
	je 22f
24:
	movzx eax, BYTE PTR [rbp+r14*1]
	xor eax, 54
	mov BYTE PTR [rbx+r14*1+32], al
	add r14, 1
	cmp r14, r13
	jne 24b
	jmp 23f
22:
23:
	mov eax, DWORD PTR [rbx+32]
	xor eax, 1785358954
	mov DWORD PTR [r12+32], eax
	mov eax, DWORD PTR [rbx+36]
	xor eax, 1785358954
	mov DWORD PTR [r12+36], eax
	mov eax, DWORD PTR [rbx+40]
	xor eax, 1785358954
	mov DWORD PTR [r12+40], eax
	mov eax, DWORD PTR [rbx+44]
	xor eax, 1785358954
	mov DWORD PTR [r12+44], eax
	mov eax, DWORD PTR [rbx+48]
	xor eax, 1785358954
	mov DWORD PTR [r12+48], eax
	mov eax, DWORD PTR [rbx+52]
	xor eax, 1785358954
	mov DWORD PTR [r12+52], eax
	mov eax, DWORD PTR [rbx+56]
	xor eax, 1785358954
	mov DWORD PTR [r12+56], eax
	mov eax, DWORD PTR [rbx+60]
	xor eax, 1785358954
	mov DWORD PTR [r12+60], eax
	mov eax, DWORD PTR [rbx+64]
	xor eax, 1785358954
	mov DWORD PTR [r12+64], eax
	mov eax, DWORD PTR [rbx+68]
	xor eax, 1785358954
	mov DWORD PTR [r12+68], eax
	mov eax, DWORD PTR [rbx+72]
	xor eax, 1785358954
	mov DWORD PTR [r12+72], eax
	mov eax, DWORD PTR [rbx+76]
	xor eax, 1785358954
	mov DWORD PTR [r12+76], eax
	mov eax, DWORD PTR [rbx+80]
	xor eax, 1785358954
	mov DWORD PTR [r12+80], eax
	mov eax, DWORD PTR [rbx+84]
	xor eax, 1785358954
	mov DWORD PTR [r12+84], eax
	mov eax, DWORD PTR [rbx+88]
	xor eax, 1785358954
	mov DWORD PTR [r12+88], eax
	mov eax, DWORD PTR [rbx+92]
	xor eax, 1785358954
	mov DWORD PTR [r12+92], eax
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+608]
	mov rbp, QWORD PTR [r15+616]
	mov r12, QWORD PTR [r15+624]
	mov r13, QWORD PTR [r15+632]
	mov r14, QWORD PTR [r15+640]
	mov r15, QWORD PTR [r15+648]
	lea rsp, [rsp+840]
21:
	ret
20:
	lea rsp, [rsp-1608]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+832], rbx
	mov QWORD PTR [r8+840], rbp
	mov QWORD PTR [r8+848], r12
	mov QWORD PTR [r8+856], r13
	mov QWORD PTR [r8+864], r14
	mov QWORD PTR [r8+872], r15
	mov r15, r8
	mov rbx, rdx
	mov rbp, rcx
	mov r12, rdi
	mov r13, rsi
	cmp rbp, 65
	jae 25f
	mov rdx, rbx
	mov rcx, rbp
	jmp 26f
25:
	mov rdi, r15
	add rdi, 1184
	call {vg_sha256_init}
	mov rdi, r15
	add rdi, 1184
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha256_update_scratch_avx2}
	mov rdi, r15
	add rdi, 1184
	mov rsi, rbp
	mov rdx, r15
	add rdx, 1344
	mov rcx, r15
	call {vg_sha256_finalize_scratch_avx2}
	mov rdx, r15
	add rdx, 1344
	mov ecx, 32
26:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rbx, QWORD PTR [r15+832]
	mov rbp, QWORD PTR [r15+840]
	mov r12, QWORD PTR [r15+848]
	mov r13, QWORD PTR [r15+856]
	mov r14, QWORD PTR [r15+864]
	mov r15, QWORD PTR [r15+872]
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	mov QWORD PTR [rsp+1032], r11
	mov QWORD PTR [rsp+1040], r11
	mov QWORD PTR [rsp+1048], r11
	mov QWORD PTR [rsp+1056], r11
	mov QWORD PTR [rsp+1064], r11
	mov QWORD PTR [rsp+1072], r11
	mov QWORD PTR [rsp+1080], r11
	mov QWORD PTR [rsp+1088], r11
	mov QWORD PTR [rsp+1096], r11
	mov QWORD PTR [rsp+1104], r11
	mov QWORD PTR [rsp+1112], r11
	mov QWORD PTR [rsp+1120], r11
	mov QWORD PTR [rsp+1128], r11
	mov QWORD PTR [rsp+1136], r11
	mov QWORD PTR [rsp+1144], r11
	mov QWORD PTR [rsp+1152], r11
	mov QWORD PTR [rsp+1160], r11
	mov QWORD PTR [rsp+1168], r11
	mov QWORD PTR [rsp+1176], r11
	mov QWORD PTR [rsp+1184], r11
	mov QWORD PTR [rsp+1192], r11
	mov QWORD PTR [rsp+1200], r11
	mov QWORD PTR [rsp+1208], r11
	mov QWORD PTR [rsp+1216], r11
	mov QWORD PTR [rsp+1224], r11
	mov QWORD PTR [rsp+1232], r11
	mov QWORD PTR [rsp+1240], r11
	mov QWORD PTR [rsp+1248], r11
	mov QWORD PTR [rsp+1256], r11
	mov QWORD PTR [rsp+1264], r11
	mov QWORD PTR [rsp+1272], r11
	mov QWORD PTR [rsp+1280], r11
	mov QWORD PTR [rsp+1288], r11
	mov QWORD PTR [rsp+1296], r11
	mov QWORD PTR [rsp+1304], r11
	mov QWORD PTR [rsp+1312], r11
	mov QWORD PTR [rsp+1320], r11
	mov QWORD PTR [rsp+1328], r11
	mov QWORD PTR [rsp+1336], r11
	mov QWORD PTR [rsp+1344], r11
	mov QWORD PTR [rsp+1352], r11
	mov QWORD PTR [rsp+1360], r11
	mov QWORD PTR [rsp+1368], r11
	mov QWORD PTR [rsp+1376], r11
	mov QWORD PTR [rsp+1384], r11
	mov QWORD PTR [rsp+1392], r11
	mov QWORD PTR [rsp+1400], r11
	mov QWORD PTR [rsp+1408], r11
	mov QWORD PTR [rsp+1416], r11
	mov QWORD PTR [rsp+1424], r11
	mov QWORD PTR [rsp+1432], r11
	mov QWORD PTR [rsp+1440], r11
	mov QWORD PTR [rsp+1448], r11
	mov QWORD PTR [rsp+1456], r11
	mov QWORD PTR [rsp+1464], r11
	mov QWORD PTR [rsp+1472], r11
	mov QWORD PTR [rsp+1480], r11
	mov QWORD PTR [rsp+1488], r11
	mov QWORD PTR [rsp+1496], r11
	mov QWORD PTR [rsp+1504], r11
	mov QWORD PTR [rsp+1512], r11
	mov QWORD PTR [rsp+1520], r11
	mov QWORD PTR [rsp+1528], r11
	mov QWORD PTR [rsp+1536], r11
	mov QWORD PTR [rsp+1544], r11
	mov QWORD PTR [rsp+1552], r11
	mov QWORD PTR [rsp+1560], r11
	mov QWORD PTR [rsp+1568], r11
	mov QWORD PTR [rsp+1576], r11
	mov QWORD PTR [rsp+1584], r11
	mov QWORD PTR [rsp+1592], r11
	mov QWORD PTR [rsp+1600], r11
	lea rsp, [rsp+1608]
	jmp 21b
	.p2align 6

vg_hmac_sha256_finalize_avx2:
	lea rsp, [rsp-840]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+608], rbx
	mov QWORD PTR [r8+616], rbp
	mov QWORD PTR [r8+624], r12
	mov QWORD PTR [r8+632], r13
	mov QWORD PTR [r8+640], r14
	mov QWORD PTR [r8+648], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 656
	mov rcx, r15
	call {vg_sha256_finalize_scratch_avx2}
	mov eax, DWORD PTR [r12]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+4]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+8]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+12]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+16]
	mov DWORD PTR [rbx+16], eax
	mov eax, DWORD PTR [r12+20]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+24]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+28]
	mov DWORD PTR [rbx+28], eax
	mov eax, DWORD PTR [r15+656]
	mov DWORD PTR [rbx+32], eax
	mov eax, DWORD PTR [r15+660]
	mov DWORD PTR [rbx+36], eax
	mov eax, DWORD PTR [r15+664]
	mov DWORD PTR [rbx+40], eax
	mov eax, DWORD PTR [r15+668]
	mov DWORD PTR [rbx+44], eax
	mov eax, DWORD PTR [r15+672]
	mov DWORD PTR [rbx+48], eax
	mov eax, DWORD PTR [r15+676]
	mov DWORD PTR [rbx+52], eax
	mov eax, DWORD PTR [r15+680]
	mov DWORD PTR [rbx+56], eax
	mov eax, DWORD PTR [r15+684]
	mov DWORD PTR [rbx+60], eax
	mov rbp, rbx
	add rbp, 32
	mov eax, 128
	mov DWORD PTR [rbp+32], eax
	mov eax, 0
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 96
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rbp, r13
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
	mov rbx, QWORD PTR [r15+608]
	mov rbp, QWORD PTR [r15+616]
	mov r12, QWORD PTR [r15+624]
	mov r13, QWORD PTR [r15+632]
	mov r14, QWORD PTR [r15+640]
	mov r15, QWORD PTR [r15+648]
	lea rsp, [rsp+840]
	ret
	.p2align 6

vg_hmac_sha256_init_scratch_avx2:
	mov QWORD PTR [r8+608], rbx
	mov QWORD PTR [r8+616], rbp
	mov QWORD PTR [r8+624], r12
	mov QWORD PTR [r8+632], r13
	mov QWORD PTR [r8+640], r14
	mov QWORD PTR [r8+648], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha256_init}
	mov rdi, r12
	call {vg_sha256_init}
	mov eax, 909522486
	mov DWORD PTR [rbx+32], eax
	mov DWORD PTR [rbx+36], eax
	mov DWORD PTR [rbx+40], eax
	mov DWORD PTR [rbx+44], eax
	mov DWORD PTR [rbx+48], eax
	mov DWORD PTR [rbx+52], eax
	mov DWORD PTR [rbx+56], eax
	mov DWORD PTR [rbx+60], eax
	mov DWORD PTR [rbx+64], eax
	mov DWORD PTR [rbx+68], eax
	mov DWORD PTR [rbx+72], eax
	mov DWORD PTR [rbx+76], eax
	mov DWORD PTR [rbx+80], eax
	mov DWORD PTR [rbx+84], eax
	mov DWORD PTR [rbx+88], eax
	mov DWORD PTR [rbx+92], eax
	mov r14d, 0
	test r13, r13
	je 20f
22:
	movzx eax, BYTE PTR [rbp+r14*1]
	xor eax, 54
	mov BYTE PTR [rbx+r14*1+32], al
	add r14, 1
	cmp r14, r13
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [rbx+32]
	xor eax, 1785358954
	mov DWORD PTR [r12+32], eax
	mov eax, DWORD PTR [rbx+36]
	xor eax, 1785358954
	mov DWORD PTR [r12+36], eax
	mov eax, DWORD PTR [rbx+40]
	xor eax, 1785358954
	mov DWORD PTR [r12+40], eax
	mov eax, DWORD PTR [rbx+44]
	xor eax, 1785358954
	mov DWORD PTR [r12+44], eax
	mov eax, DWORD PTR [rbx+48]
	xor eax, 1785358954
	mov DWORD PTR [r12+48], eax
	mov eax, DWORD PTR [rbx+52]
	xor eax, 1785358954
	mov DWORD PTR [r12+52], eax
	mov eax, DWORD PTR [rbx+56]
	xor eax, 1785358954
	mov DWORD PTR [r12+56], eax
	mov eax, DWORD PTR [rbx+60]
	xor eax, 1785358954
	mov DWORD PTR [r12+60], eax
	mov eax, DWORD PTR [rbx+64]
	xor eax, 1785358954
	mov DWORD PTR [r12+64], eax
	mov eax, DWORD PTR [rbx+68]
	xor eax, 1785358954
	mov DWORD PTR [r12+68], eax
	mov eax, DWORD PTR [rbx+72]
	xor eax, 1785358954
	mov DWORD PTR [r12+72], eax
	mov eax, DWORD PTR [rbx+76]
	xor eax, 1785358954
	mov DWORD PTR [r12+76], eax
	mov eax, DWORD PTR [rbx+80]
	xor eax, 1785358954
	mov DWORD PTR [r12+80], eax
	mov eax, DWORD PTR [rbx+84]
	xor eax, 1785358954
	mov DWORD PTR [r12+84], eax
	mov eax, DWORD PTR [rbx+88]
	xor eax, 1785358954
	mov DWORD PTR [r12+88], eax
	mov eax, DWORD PTR [rbx+92]
	xor eax, 1785358954
	mov DWORD PTR [r12+92], eax
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+608]
	mov rbp, QWORD PTR [r15+616]
	mov r12, QWORD PTR [r15+624]
	mov r13, QWORD PTR [r15+632]
	mov r14, QWORD PTR [r15+640]
	mov r15, QWORD PTR [r15+648]
	ret
	.p2align 6

vg_hmac_sha256_finalize_scratch_avx2:
	mov QWORD PTR [r8+608], rbx
	mov QWORD PTR [r8+616], rbp
	mov QWORD PTR [r8+624], r12
	mov QWORD PTR [r8+632], r13
	mov QWORD PTR [r8+640], r14
	mov QWORD PTR [r8+648], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 656
	mov rcx, r15
	call {vg_sha256_finalize_scratch_avx2}
	mov eax, DWORD PTR [r12]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+4]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+8]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+12]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+16]
	mov DWORD PTR [rbx+16], eax
	mov eax, DWORD PTR [r12+20]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+24]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+28]
	mov DWORD PTR [rbx+28], eax
	mov eax, DWORD PTR [r15+656]
	mov DWORD PTR [rbx+32], eax
	mov eax, DWORD PTR [r15+660]
	mov DWORD PTR [rbx+36], eax
	mov eax, DWORD PTR [r15+664]
	mov DWORD PTR [rbx+40], eax
	mov eax, DWORD PTR [r15+668]
	mov DWORD PTR [rbx+44], eax
	mov eax, DWORD PTR [r15+672]
	mov DWORD PTR [rbx+48], eax
	mov eax, DWORD PTR [r15+676]
	mov DWORD PTR [rbx+52], eax
	mov eax, DWORD PTR [r15+680]
	mov DWORD PTR [rbx+56], eax
	mov eax, DWORD PTR [r15+684]
	mov DWORD PTR [rbx+60], eax
	mov rbp, rbx
	add rbp, 32
	mov eax, 128
	mov DWORD PTR [rbp+32], eax
	mov eax, 0
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 96
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rbp, r13
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
	mov rbx, QWORD PTR [r15+608]
	mov rbp, QWORD PTR [r15+616]
	mov r12, QWORD PTR [r15+624]
	mov r13, QWORD PTR [r15+632]
	mov r14, QWORD PTR [r15+640]
	mov r15, QWORD PTR [r15+648]
	ret
	.p2align 6

vg_hmac_sha256_init_shani:
	cmp rcx, 65
	jae 20f
	lea rsp, [rsp-840]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+608], rbx
	mov QWORD PTR [r8+616], rbp
	mov QWORD PTR [r8+624], r12
	mov QWORD PTR [r8+632], r13
	mov QWORD PTR [r8+640], r14
	mov QWORD PTR [r8+648], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha256_init}
	mov rdi, r12
	call {vg_sha256_init}
	mov eax, 909522486
	mov DWORD PTR [rbx+32], eax
	mov DWORD PTR [rbx+36], eax
	mov DWORD PTR [rbx+40], eax
	mov DWORD PTR [rbx+44], eax
	mov DWORD PTR [rbx+48], eax
	mov DWORD PTR [rbx+52], eax
	mov DWORD PTR [rbx+56], eax
	mov DWORD PTR [rbx+60], eax
	mov DWORD PTR [rbx+64], eax
	mov DWORD PTR [rbx+68], eax
	mov DWORD PTR [rbx+72], eax
	mov DWORD PTR [rbx+76], eax
	mov DWORD PTR [rbx+80], eax
	mov DWORD PTR [rbx+84], eax
	mov DWORD PTR [rbx+88], eax
	mov DWORD PTR [rbx+92], eax
	mov r14d, 0
	test r13, r13
	je 22f
24:
	movzx eax, BYTE PTR [rbp+r14*1]
	xor eax, 54
	mov BYTE PTR [rbx+r14*1+32], al
	add r14, 1
	cmp r14, r13
	jne 24b
	jmp 23f
22:
23:
	mov eax, DWORD PTR [rbx+32]
	xor eax, 1785358954
	mov DWORD PTR [r12+32], eax
	mov eax, DWORD PTR [rbx+36]
	xor eax, 1785358954
	mov DWORD PTR [r12+36], eax
	mov eax, DWORD PTR [rbx+40]
	xor eax, 1785358954
	mov DWORD PTR [r12+40], eax
	mov eax, DWORD PTR [rbx+44]
	xor eax, 1785358954
	mov DWORD PTR [r12+44], eax
	mov eax, DWORD PTR [rbx+48]
	xor eax, 1785358954
	mov DWORD PTR [r12+48], eax
	mov eax, DWORD PTR [rbx+52]
	xor eax, 1785358954
	mov DWORD PTR [r12+52], eax
	mov eax, DWORD PTR [rbx+56]
	xor eax, 1785358954
	mov DWORD PTR [r12+56], eax
	mov eax, DWORD PTR [rbx+60]
	xor eax, 1785358954
	mov DWORD PTR [r12+60], eax
	mov eax, DWORD PTR [rbx+64]
	xor eax, 1785358954
	mov DWORD PTR [r12+64], eax
	mov eax, DWORD PTR [rbx+68]
	xor eax, 1785358954
	mov DWORD PTR [r12+68], eax
	mov eax, DWORD PTR [rbx+72]
	xor eax, 1785358954
	mov DWORD PTR [r12+72], eax
	mov eax, DWORD PTR [rbx+76]
	xor eax, 1785358954
	mov DWORD PTR [r12+76], eax
	mov eax, DWORD PTR [rbx+80]
	xor eax, 1785358954
	mov DWORD PTR [r12+80], eax
	mov eax, DWORD PTR [rbx+84]
	xor eax, 1785358954
	mov DWORD PTR [r12+84], eax
	mov eax, DWORD PTR [rbx+88]
	xor eax, 1785358954
	mov DWORD PTR [r12+88], eax
	mov eax, DWORD PTR [rbx+92]
	xor eax, 1785358954
	mov DWORD PTR [r12+92], eax
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+608]
	mov rbp, QWORD PTR [r15+616]
	mov r12, QWORD PTR [r15+624]
	mov r13, QWORD PTR [r15+632]
	mov r14, QWORD PTR [r15+640]
	mov r15, QWORD PTR [r15+648]
	lea rsp, [rsp+840]
21:
	ret
20:
	lea rsp, [rsp-1608]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+832], rbx
	mov QWORD PTR [r8+840], rbp
	mov QWORD PTR [r8+848], r12
	mov QWORD PTR [r8+856], r13
	mov QWORD PTR [r8+864], r14
	mov QWORD PTR [r8+872], r15
	mov r15, r8
	mov rbx, rdx
	mov rbp, rcx
	mov r12, rdi
	mov r13, rsi
	cmp rbp, 65
	jae 25f
	mov rdx, rbx
	mov rcx, rbp
	jmp 26f
25:
	mov rdi, r15
	add rdi, 1184
	call {vg_sha256_init}
	mov rdi, r15
	add rdi, 1184
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha256_update_scratch_shani}
	mov rdi, r15
	add rdi, 1184
	mov rsi, rbp
	mov rdx, r15
	add rdx, 1344
	mov rcx, r15
	call {vg_sha256_finalize_scratch_shani}
	mov rdx, r15
	add rdx, 1344
	mov ecx, 32
26:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha256_init_scratch_shani}
	mov rbx, QWORD PTR [r15+832]
	mov rbp, QWORD PTR [r15+840]
	mov r12, QWORD PTR [r15+848]
	mov r13, QWORD PTR [r15+856]
	mov r14, QWORD PTR [r15+864]
	mov r15, QWORD PTR [r15+872]
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	mov QWORD PTR [rsp+1032], r11
	mov QWORD PTR [rsp+1040], r11
	mov QWORD PTR [rsp+1048], r11
	mov QWORD PTR [rsp+1056], r11
	mov QWORD PTR [rsp+1064], r11
	mov QWORD PTR [rsp+1072], r11
	mov QWORD PTR [rsp+1080], r11
	mov QWORD PTR [rsp+1088], r11
	mov QWORD PTR [rsp+1096], r11
	mov QWORD PTR [rsp+1104], r11
	mov QWORD PTR [rsp+1112], r11
	mov QWORD PTR [rsp+1120], r11
	mov QWORD PTR [rsp+1128], r11
	mov QWORD PTR [rsp+1136], r11
	mov QWORD PTR [rsp+1144], r11
	mov QWORD PTR [rsp+1152], r11
	mov QWORD PTR [rsp+1160], r11
	mov QWORD PTR [rsp+1168], r11
	mov QWORD PTR [rsp+1176], r11
	mov QWORD PTR [rsp+1184], r11
	mov QWORD PTR [rsp+1192], r11
	mov QWORD PTR [rsp+1200], r11
	mov QWORD PTR [rsp+1208], r11
	mov QWORD PTR [rsp+1216], r11
	mov QWORD PTR [rsp+1224], r11
	mov QWORD PTR [rsp+1232], r11
	mov QWORD PTR [rsp+1240], r11
	mov QWORD PTR [rsp+1248], r11
	mov QWORD PTR [rsp+1256], r11
	mov QWORD PTR [rsp+1264], r11
	mov QWORD PTR [rsp+1272], r11
	mov QWORD PTR [rsp+1280], r11
	mov QWORD PTR [rsp+1288], r11
	mov QWORD PTR [rsp+1296], r11
	mov QWORD PTR [rsp+1304], r11
	mov QWORD PTR [rsp+1312], r11
	mov QWORD PTR [rsp+1320], r11
	mov QWORD PTR [rsp+1328], r11
	mov QWORD PTR [rsp+1336], r11
	mov QWORD PTR [rsp+1344], r11
	mov QWORD PTR [rsp+1352], r11
	mov QWORD PTR [rsp+1360], r11
	mov QWORD PTR [rsp+1368], r11
	mov QWORD PTR [rsp+1376], r11
	mov QWORD PTR [rsp+1384], r11
	mov QWORD PTR [rsp+1392], r11
	mov QWORD PTR [rsp+1400], r11
	mov QWORD PTR [rsp+1408], r11
	mov QWORD PTR [rsp+1416], r11
	mov QWORD PTR [rsp+1424], r11
	mov QWORD PTR [rsp+1432], r11
	mov QWORD PTR [rsp+1440], r11
	mov QWORD PTR [rsp+1448], r11
	mov QWORD PTR [rsp+1456], r11
	mov QWORD PTR [rsp+1464], r11
	mov QWORD PTR [rsp+1472], r11
	mov QWORD PTR [rsp+1480], r11
	mov QWORD PTR [rsp+1488], r11
	mov QWORD PTR [rsp+1496], r11
	mov QWORD PTR [rsp+1504], r11
	mov QWORD PTR [rsp+1512], r11
	mov QWORD PTR [rsp+1520], r11
	mov QWORD PTR [rsp+1528], r11
	mov QWORD PTR [rsp+1536], r11
	mov QWORD PTR [rsp+1544], r11
	mov QWORD PTR [rsp+1552], r11
	mov QWORD PTR [rsp+1560], r11
	mov QWORD PTR [rsp+1568], r11
	mov QWORD PTR [rsp+1576], r11
	mov QWORD PTR [rsp+1584], r11
	mov QWORD PTR [rsp+1592], r11
	mov QWORD PTR [rsp+1600], r11
	lea rsp, [rsp+1608]
	jmp 21b
	.p2align 6

vg_hmac_sha256_finalize_shani:
	lea rsp, [rsp-840]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+608], rbx
	mov QWORD PTR [r8+616], rbp
	mov QWORD PTR [r8+624], r12
	mov QWORD PTR [r8+632], r13
	mov QWORD PTR [r8+640], r14
	mov QWORD PTR [r8+648], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 656
	mov rcx, r15
	call {vg_sha256_finalize_scratch_shani}
	mov eax, DWORD PTR [r12]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+4]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+8]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+12]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+16]
	mov DWORD PTR [rbx+16], eax
	mov eax, DWORD PTR [r12+20]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+24]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+28]
	mov DWORD PTR [rbx+28], eax
	mov eax, DWORD PTR [r15+656]
	mov DWORD PTR [rbx+32], eax
	mov eax, DWORD PTR [r15+660]
	mov DWORD PTR [rbx+36], eax
	mov eax, DWORD PTR [r15+664]
	mov DWORD PTR [rbx+40], eax
	mov eax, DWORD PTR [r15+668]
	mov DWORD PTR [rbx+44], eax
	mov eax, DWORD PTR [r15+672]
	mov DWORD PTR [rbx+48], eax
	mov eax, DWORD PTR [r15+676]
	mov DWORD PTR [rbx+52], eax
	mov eax, DWORD PTR [r15+680]
	mov DWORD PTR [rbx+56], eax
	mov eax, DWORD PTR [r15+684]
	mov DWORD PTR [rbx+60], eax
	mov rbp, rbx
	add rbp, 32
	mov eax, 128
	mov DWORD PTR [rbp+32], eax
	mov eax, 0
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 96
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rbp, r13
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
	mov rbx, QWORD PTR [r15+608]
	mov rbp, QWORD PTR [r15+616]
	mov r12, QWORD PTR [r15+624]
	mov r13, QWORD PTR [r15+632]
	mov r14, QWORD PTR [r15+640]
	mov r15, QWORD PTR [r15+648]
	lea rsp, [rsp+840]
	ret
	.p2align 6

vg_hmac_sha256_init_scratch_shani:
	mov QWORD PTR [r8+608], rbx
	mov QWORD PTR [r8+616], rbp
	mov QWORD PTR [r8+624], r12
	mov QWORD PTR [r8+632], r13
	mov QWORD PTR [r8+640], r14
	mov QWORD PTR [r8+648], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha256_init}
	mov rdi, r12
	call {vg_sha256_init}
	mov eax, 909522486
	mov DWORD PTR [rbx+32], eax
	mov DWORD PTR [rbx+36], eax
	mov DWORD PTR [rbx+40], eax
	mov DWORD PTR [rbx+44], eax
	mov DWORD PTR [rbx+48], eax
	mov DWORD PTR [rbx+52], eax
	mov DWORD PTR [rbx+56], eax
	mov DWORD PTR [rbx+60], eax
	mov DWORD PTR [rbx+64], eax
	mov DWORD PTR [rbx+68], eax
	mov DWORD PTR [rbx+72], eax
	mov DWORD PTR [rbx+76], eax
	mov DWORD PTR [rbx+80], eax
	mov DWORD PTR [rbx+84], eax
	mov DWORD PTR [rbx+88], eax
	mov DWORD PTR [rbx+92], eax
	mov r14d, 0
	test r13, r13
	je 20f
22:
	movzx eax, BYTE PTR [rbp+r14*1]
	xor eax, 54
	mov BYTE PTR [rbx+r14*1+32], al
	add r14, 1
	cmp r14, r13
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [rbx+32]
	xor eax, 1785358954
	mov DWORD PTR [r12+32], eax
	mov eax, DWORD PTR [rbx+36]
	xor eax, 1785358954
	mov DWORD PTR [r12+36], eax
	mov eax, DWORD PTR [rbx+40]
	xor eax, 1785358954
	mov DWORD PTR [r12+40], eax
	mov eax, DWORD PTR [rbx+44]
	xor eax, 1785358954
	mov DWORD PTR [r12+44], eax
	mov eax, DWORD PTR [rbx+48]
	xor eax, 1785358954
	mov DWORD PTR [r12+48], eax
	mov eax, DWORD PTR [rbx+52]
	xor eax, 1785358954
	mov DWORD PTR [r12+52], eax
	mov eax, DWORD PTR [rbx+56]
	xor eax, 1785358954
	mov DWORD PTR [r12+56], eax
	mov eax, DWORD PTR [rbx+60]
	xor eax, 1785358954
	mov DWORD PTR [r12+60], eax
	mov eax, DWORD PTR [rbx+64]
	xor eax, 1785358954
	mov DWORD PTR [r12+64], eax
	mov eax, DWORD PTR [rbx+68]
	xor eax, 1785358954
	mov DWORD PTR [r12+68], eax
	mov eax, DWORD PTR [rbx+72]
	xor eax, 1785358954
	mov DWORD PTR [r12+72], eax
	mov eax, DWORD PTR [rbx+76]
	xor eax, 1785358954
	mov DWORD PTR [r12+76], eax
	mov eax, DWORD PTR [rbx+80]
	xor eax, 1785358954
	mov DWORD PTR [r12+80], eax
	mov eax, DWORD PTR [rbx+84]
	xor eax, 1785358954
	mov DWORD PTR [r12+84], eax
	mov eax, DWORD PTR [rbx+88]
	xor eax, 1785358954
	mov DWORD PTR [r12+88], eax
	mov eax, DWORD PTR [rbx+92]
	xor eax, 1785358954
	mov DWORD PTR [r12+92], eax
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+608]
	mov rbp, QWORD PTR [r15+616]
	mov r12, QWORD PTR [r15+624]
	mov r13, QWORD PTR [r15+632]
	mov r14, QWORD PTR [r15+640]
	mov r15, QWORD PTR [r15+648]
	ret
	.p2align 6

vg_hmac_sha256_finalize_scratch_shani:
	mov QWORD PTR [r8+608], rbx
	mov QWORD PTR [r8+616], rbp
	mov QWORD PTR [r8+624], r12
	mov QWORD PTR [r8+632], r13
	mov QWORD PTR [r8+640], r14
	mov QWORD PTR [r8+648], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 656
	mov rcx, r15
	call {vg_sha256_finalize_scratch_shani}
	mov eax, DWORD PTR [r12]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+4]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+8]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+12]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+16]
	mov DWORD PTR [rbx+16], eax
	mov eax, DWORD PTR [r12+20]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+24]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+28]
	mov DWORD PTR [rbx+28], eax
	mov eax, DWORD PTR [r15+656]
	mov DWORD PTR [rbx+32], eax
	mov eax, DWORD PTR [r15+660]
	mov DWORD PTR [rbx+36], eax
	mov eax, DWORD PTR [r15+664]
	mov DWORD PTR [rbx+40], eax
	mov eax, DWORD PTR [r15+668]
	mov DWORD PTR [rbx+44], eax
	mov eax, DWORD PTR [r15+672]
	mov DWORD PTR [rbx+48], eax
	mov eax, DWORD PTR [r15+676]
	mov DWORD PTR [rbx+52], eax
	mov eax, DWORD PTR [r15+680]
	mov DWORD PTR [rbx+56], eax
	mov eax, DWORD PTR [r15+684]
	mov DWORD PTR [rbx+60], eax
	mov rbp, rbx
	add rbp, 32
	mov eax, 128
	mov DWORD PTR [rbp+32], eax
	mov eax, 0
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 96
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rbp, r13
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
	mov rbx, QWORD PTR [r15+608]
	mov rbp, QWORD PTR [r15+616]
	mov r12, QWORD PTR [r15+624]
	mov r13, QWORD PTR [r15+632]
	mov r14, QWORD PTR [r15+640]
	mov r15, QWORD PTR [r15+648]
	ret
	.p2align 6
