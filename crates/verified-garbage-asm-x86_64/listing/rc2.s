// The functions of `src/rc2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_init:
	lea rsp, [rsp-592]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov eax, 1
	mov r10, rsi
	sub r10, 1
	cmp r10, 128
	jae 20f
	mov eax, 2
	mov r10, rdx
	sub r10, 1
	cmp r10, 1024
	jae 22f
	mov eax, 3
	cmp r8, 8
	jne 24f
	mov eax, 0
	jmp 25f
24:
25:
	jmp 23f
22:
23:
	jmp 21f
20:
21:
	test rax, rax
	jne 26f
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r9+128], rax
	mov rcx, r9
	mov r8, QWORD PTR [rsp+8]
	call {vg_rc2_expand_key}
	mov eax, 0
	jmp 27f
26:
27:
	mov r11d, 0
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
	lea rsp, [rsp+592]
	ret
	.p2align 6

vg_rc2_cbc_encrypt_update:
	lea rsp, [rsp-592]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	test r9, r9
	je 20f
	mov r10d, 0
	test rsi, rsi
	je 22f
24:
	movzx r11d, BYTE PTR [rdi+r10*1+136]
	mov BYTE PTR [r8+r10*1], r11b
	add r10, 1
	cmp r10, rsi
	jne 24b
	jmp 23f
22:
23:
	sub r9, rsi
	add r8, rsi
	mov r10d, 0
	test r9, r9
	je 25f
27:
	movzx r11d, BYTE PTR [rdx+r10*1]
	mov BYTE PTR [r8+r10*1], r11b
	add r10, 1
	cmp r10, r9
	jne 27b
	jmp 26f
25:
26:
	add rdx, r9
	sub rcx, r9
	mov r10d, 0
	test rcx, rcx
	je 28f
210:
	movzx r11d, BYTE PTR [rdx+r10*1]
	mov BYTE PTR [rdi+r10*1+136], r11b
	add r10, 1
	cmp r10, rcx
	jne 210b
	jmp 29f
28:
29:
	sub r8, rsi
	add r9, rsi
	shr r9, 3
	mov rdx, r8
	mov rcx, r9
	mov rsi, rdi
	add rsi, 128
	mov r8, QWORD PTR [rsp+8]
	call {vg_rc2_cbc_encrypt}
	jmp 21f
20:
	mov rax, rdi
	add rax, rsi
	mov r10d, 0
	test rcx, rcx
	je 211f
213:
	movzx r11d, BYTE PTR [rdx+r10*1]
	mov BYTE PTR [rax+r10*1+136], r11b
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
21:
	mov r11d, 0
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
	lea rsp, [rsp+592]
	ret
	.p2align 6

vg_rc2_cbc_decrypt_update:
	lea rsp, [rsp-592]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	test r9, r9
	je 20f
	mov r10d, 0
	test rsi, rsi
	je 22f
24:
	movzx r11d, BYTE PTR [rdi+r10*1+136]
	mov BYTE PTR [r8+r10*1], r11b
	add r10, 1
	cmp r10, rsi
	jne 24b
	jmp 23f
22:
23:
	sub r9, rsi
	add r8, rsi
	mov r10d, 0
	test r9, r9
	je 25f
27:
	movzx r11d, BYTE PTR [rdx+r10*1]
	mov BYTE PTR [r8+r10*1], r11b
	add r10, 1
	cmp r10, r9
	jne 27b
	jmp 26f
25:
26:
	add rdx, r9
	sub rcx, r9
	mov r10d, 0
	test rcx, rcx
	je 28f
210:
	movzx r11d, BYTE PTR [rdx+r10*1]
	mov BYTE PTR [rdi+r10*1+136], r11b
	add r10, 1
	cmp r10, rcx
	jne 210b
	jmp 29f
28:
29:
	sub r8, rsi
	add r9, rsi
	shr r9, 3
	mov rdx, r8
	mov rcx, r9
	mov rsi, rdi
	add rsi, 128
	mov r8, QWORD PTR [rsp+8]
	call {vg_rc2_cbc_decrypt}
	jmp 21f
20:
	mov rax, rdi
	add rax, rsi
	mov r10d, 0
	test rcx, rcx
	je 211f
213:
	movzx r11d, BYTE PTR [rdx+r10*1]
	mov BYTE PTR [rax+r10*1+136], r11b
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
21:
	mov r11d, 0
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
	lea rsp, [rsp+592]
	ret
	.p2align 6

vg_rc2_cbc_encrypt:
	mov QWORD PTR [r8+264], rbx
	mov QWORD PTR [r8+272], rbp
	mov rbx, rsi
	mov rbp, rcx
	mov rsi, rdx
	mov rdx, r8
	cmp rbp, 0
	je 20f
22:
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rbx]
	mov QWORD PTR [rsi], rax
	call {vg_rc2_encrypt_block}
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx], rax
	add rsi, 8
	sub rbp, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [rdx+264]
	mov rbp, QWORD PTR [rdx+272]
	ret
	.p2align 6

vg_rc2_cbc_decrypt:
	mov QWORD PTR [r8+264], rbx
	mov QWORD PTR [r8+272], rbp
	mov rbx, rsi
	mov rbp, rcx
	mov rsi, rdx
	mov rdx, r8
	cmp rbp, 0
	je 20f
22:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdx+256], rax
	call {vg_rc2_decrypt_block}
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rbx]
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rdx+256]
	mov QWORD PTR [rbx], rax
	add rsi, 8
	sub rbp, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [rdx+264]
	mov rbp, QWORD PTR [rdx+272]
	ret
	.p2align 6

vg_rc2_expand_key:
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r12, rdi
	mov r13, rsi
	mov r14, rcx
	mov r15, rdx
	mov rbx, 0
20:
	movzx eax, BYTE PTR [r12+rbx*1]
	mov BYTE PTR [r14+rbx*1], al
	add rbx, 1
	cmp rbx, r13
	jne 20b
	cmp rbx, 128
	jne 21f
	jmp 22f
21:
23:
	movzx eax, BYTE PTR [r14+rbx*1-1]
	mov r9, rbx
	sub r9, r13
	movzx ecx, BYTE PTR [r14+r9*1]
	add rax, rcx
	and rax, 255
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movabs r10, 55170164890009817
	movq xmm4, r10
	movabs r10, 66710346883989529
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 34059558823985192
	movq xmm4, r10
	movabs r10, 44192499066994762
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 36873458180554950
	movq xmm4, r10
	movabs r10, 39969803182932011
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 38281026334359650
	movq xmm4, r10
	movabs r10, 45600024273027140
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 68961751556292631
	movq xmm4, r10
	movabs r10, 5348363871649927
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 39688439872159841
	movq xmm4, r10
	movabs r10, 14074285714898953
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 66146894414282941
	movq xmm4, r10
	movabs r10, 3096753036787846
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 9570290951848176
	movq xmm4, r10
	movabs r10, 36592081986846812
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 41377255382188116
	movq xmm4, r10
	movabs r10, 7882063858368718
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 5630324173570163
	movq xmm4, r10
	movabs r10, 61925529972637863
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 8726591869091858
	movq xmm4, r10
	movabs r10, 58829249397522491
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 13511709419176002
	movq xmm4, r10
	movabs r10, 10696830802985123
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 61361605064982639
	movq xmm4, r10
	movabs r10, 24488353045479494
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 43628745960063015
	movq xmm4, r10
	movabs r10, 844712702640316
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 69243698970427640
	movq xmm4, r10
	movabs r10, 65020985923797136
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 13230238746214406
	movq xmm4, r10
	movabs r10, 60517248848494792
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 62488449867317256
	movq xmm4, r10
	movabs r10, 69525341455122560
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 48414185631645828
	movq xmm4, r10
	movabs r10, 11822404293427253
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 31807574313140374
	movq xmm4, r10
	movabs r10, 32651410832425050
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 26459541174419531
	movq xmm4, r10
	movabs r10, 66428798879924228
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 30962526625726658
	movq xmm4, r10
	movabs r10, 57421767132643343
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 22518749765632036
	movq xmm4, r10
	movabs r10, 16044554724835489
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 37436421018747033
	movq xmm4, r10
	movabs r10, 34340720264871971
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 25614454809035004
	movq xmm4, r10
	movabs r10, 13792922404454437
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 42785270207938605
	movq xmm4, r10
	movabs r10, 48977273021923555
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 4503775735644165
	movq xmm4, r10
	movabs r10, 56577269189836903
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 58266308021584083
	movq xmm4, r10
	movabs r10, 12385620540129505
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 17732927829180515
	movq xmm4, r10
	movabs r10, 47569859489431640
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 7600047713157133
	movq xmm4, r10
	movabs r10, 49540691121078443
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 26740174331838651
	movq xmm4, r10
	movabs r10, 12948729408585913
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 19985663960219845
	movq xmm4, r10
	movabs r10, 33496192254279909
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 29273535027740682
	movq xmm4, r10
	movabs r10, 48695999907954942
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	mov BYTE PTR [r14+rbx*1], al
	add rbx, 1
	cmp rbx, 128
	jne 23b
22:
	mov rbp, r15
	add rbp, 7
	shr rbp, 3
	mov rbx, 128
	sub rbx, rbp
	mov r9, r15
	and r9, 7
	mov rdx, 255
	cmp r9, 1
	je 24f
	jmp 25f
24:
	mov rdx, 1
25:
	cmp r9, 2
	je 26f
	jmp 27f
26:
	mov rdx, 3
27:
	cmp r9, 3
	je 28f
	jmp 29f
28:
	mov rdx, 7
29:
	cmp r9, 4
	je 210f
	jmp 211f
210:
	mov rdx, 15
211:
	cmp r9, 5
	je 212f
	jmp 213f
212:
	mov rdx, 31
213:
	cmp r9, 6
	je 214f
	jmp 215f
214:
	mov rdx, 63
215:
	cmp r9, 7
	je 216f
	jmp 217f
216:
	mov rdx, 127
217:
	movzx eax, BYTE PTR [r14+rbx*1]
	and rax, rdx
	and rax, 255
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movabs r10, 55170164890009817
	movq xmm4, r10
	movabs r10, 66710346883989529
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 34059558823985192
	movq xmm4, r10
	movabs r10, 44192499066994762
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 36873458180554950
	movq xmm4, r10
	movabs r10, 39969803182932011
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 38281026334359650
	movq xmm4, r10
	movabs r10, 45600024273027140
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 68961751556292631
	movq xmm4, r10
	movabs r10, 5348363871649927
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 39688439872159841
	movq xmm4, r10
	movabs r10, 14074285714898953
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 66146894414282941
	movq xmm4, r10
	movabs r10, 3096753036787846
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 9570290951848176
	movq xmm4, r10
	movabs r10, 36592081986846812
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 41377255382188116
	movq xmm4, r10
	movabs r10, 7882063858368718
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 5630324173570163
	movq xmm4, r10
	movabs r10, 61925529972637863
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 8726591869091858
	movq xmm4, r10
	movabs r10, 58829249397522491
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 13511709419176002
	movq xmm4, r10
	movabs r10, 10696830802985123
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 61361605064982639
	movq xmm4, r10
	movabs r10, 24488353045479494
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 43628745960063015
	movq xmm4, r10
	movabs r10, 844712702640316
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 69243698970427640
	movq xmm4, r10
	movabs r10, 65020985923797136
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 13230238746214406
	movq xmm4, r10
	movabs r10, 60517248848494792
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 62488449867317256
	movq xmm4, r10
	movabs r10, 69525341455122560
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 48414185631645828
	movq xmm4, r10
	movabs r10, 11822404293427253
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 31807574313140374
	movq xmm4, r10
	movabs r10, 32651410832425050
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 26459541174419531
	movq xmm4, r10
	movabs r10, 66428798879924228
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 30962526625726658
	movq xmm4, r10
	movabs r10, 57421767132643343
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 22518749765632036
	movq xmm4, r10
	movabs r10, 16044554724835489
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 37436421018747033
	movq xmm4, r10
	movabs r10, 34340720264871971
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 25614454809035004
	movq xmm4, r10
	movabs r10, 13792922404454437
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 42785270207938605
	movq xmm4, r10
	movabs r10, 48977273021923555
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 4503775735644165
	movq xmm4, r10
	movabs r10, 56577269189836903
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 58266308021584083
	movq xmm4, r10
	movabs r10, 12385620540129505
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 17732927829180515
	movq xmm4, r10
	movabs r10, 47569859489431640
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 7600047713157133
	movq xmm4, r10
	movabs r10, 49540691121078443
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 26740174331838651
	movq xmm4, r10
	movabs r10, 12948729408585913
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 19985663960219845
	movq xmm4, r10
	movabs r10, 33496192254279909
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 29273535027740682
	movq xmm4, r10
	movabs r10, 48695999907954942
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	mov BYTE PTR [r14+rbx*1], al
	cmp rbx, 0
	jne 218f
	jmp 219f
218:
220:
	sub rbx, 1
	movzx eax, BYTE PTR [r14+rbx*1+1]
	mov r9, rbx
	add r9, rbp
	movzx ecx, BYTE PTR [r14+r9*1]
	xor rax, rcx
	and rax, 255
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movabs r10, 55170164890009817
	movq xmm4, r10
	movabs r10, 66710346883989529
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 34059558823985192
	movq xmm4, r10
	movabs r10, 44192499066994762
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 36873458180554950
	movq xmm4, r10
	movabs r10, 39969803182932011
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 38281026334359650
	movq xmm4, r10
	movabs r10, 45600024273027140
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 68961751556292631
	movq xmm4, r10
	movabs r10, 5348363871649927
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 39688439872159841
	movq xmm4, r10
	movabs r10, 14074285714898953
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 66146894414282941
	movq xmm4, r10
	movabs r10, 3096753036787846
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 9570290951848176
	movq xmm4, r10
	movabs r10, 36592081986846812
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 41377255382188116
	movq xmm4, r10
	movabs r10, 7882063858368718
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 5630324173570163
	movq xmm4, r10
	movabs r10, 61925529972637863
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 8726591869091858
	movq xmm4, r10
	movabs r10, 58829249397522491
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 13511709419176002
	movq xmm4, r10
	movabs r10, 10696830802985123
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 61361605064982639
	movq xmm4, r10
	movabs r10, 24488353045479494
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 43628745960063015
	movq xmm4, r10
	movabs r10, 844712702640316
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 69243698970427640
	movq xmm4, r10
	movabs r10, 65020985923797136
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 13230238746214406
	movq xmm4, r10
	movabs r10, 60517248848494792
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 62488449867317256
	movq xmm4, r10
	movabs r10, 69525341455122560
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 48414185631645828
	movq xmm4, r10
	movabs r10, 11822404293427253
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 31807574313140374
	movq xmm4, r10
	movabs r10, 32651410832425050
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 26459541174419531
	movq xmm4, r10
	movabs r10, 66428798879924228
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 30962526625726658
	movq xmm4, r10
	movabs r10, 57421767132643343
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 22518749765632036
	movq xmm4, r10
	movabs r10, 16044554724835489
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 37436421018747033
	movq xmm4, r10
	movabs r10, 34340720264871971
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 25614454809035004
	movq xmm4, r10
	movabs r10, 13792922404454437
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 42785270207938605
	movq xmm4, r10
	movabs r10, 48977273021923555
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 4503775735644165
	movq xmm4, r10
	movabs r10, 56577269189836903
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 58266308021584083
	movq xmm4, r10
	movabs r10, 12385620540129505
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 17732927829180515
	movq xmm4, r10
	movabs r10, 47569859489431640
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 7600047713157133
	movq xmm4, r10
	movabs r10, 49540691121078443
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 26740174331838651
	movq xmm4, r10
	movabs r10, 12948729408585913
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 19985663960219845
	movq xmm4, r10
	movabs r10, 33496192254279909
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movabs r10, 29273535027740682
	movq xmm4, r10
	movabs r10, 48695999907954942
	movq xmm5, r10
	punpcklqdq xmm4, xmm5
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	mov BYTE PTR [r14+rbx*1], al
	cmp rbx, 0
	jne 220b
219:
	mov rbx, QWORD PTR [r8]
	mov rbp, QWORD PTR [r8+8]
	mov r12, QWORD PTR [r8+16]
	mov r13, QWORD PTR [r8+24]
	mov r14, QWORD PTR [r8+32]
	mov r15, QWORD PTR [r8+40]
	ret
	.p2align 6

vg_rc2_encrypt_block:
	mov QWORD PTR [rdx], r12
	mov QWORD PTR [rdx+8], r13
	mov QWORD PTR [rdx+16], r14
	mov QWORD PTR [rdx+24], r15
	mov rax, QWORD PTR [rsi]
	mov r12, rax
	and r12, 65535
	mov r13, rax
	shr r13, 16
	and r13, 65535
	mov r14, rax
	shr r14, 32
	and r14, 65535
	mov r15, rax
	shr r15, 48
	and r15, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi]
	movzx r9d, BYTE PTR [rdi+1]
	ror r9, 56
	or r8, r9
	add r12, r8
	add r12, r10
	and r12, 65535
	mov rax, r12
	shr rax, 15
	ror r12, 63
	or r12, rax
	and r12, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+2]
	movzx r9d, BYTE PTR [rdi+3]
	ror r9, 56
	or r8, r9
	add r13, r8
	add r13, r10
	and r13, 65535
	mov rax, r13
	shr rax, 14
	ror r13, 62
	or r13, rax
	and r13, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+4]
	movzx r9d, BYTE PTR [rdi+5]
	ror r9, 56
	or r8, r9
	add r14, r8
	add r14, r10
	and r14, 65535
	mov rax, r14
	shr rax, 13
	ror r14, 61
	or r14, rax
	and r14, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+6]
	movzx r9d, BYTE PTR [rdi+7]
	ror r9, 56
	or r8, r9
	add r15, r8
	add r15, r10
	and r15, 65535
	mov rax, r15
	shr rax, 11
	ror r15, 59
	or r15, rax
	and r15, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+8]
	movzx r9d, BYTE PTR [rdi+9]
	ror r9, 56
	or r8, r9
	add r12, r8
	add r12, r10
	and r12, 65535
	mov rax, r12
	shr rax, 15
	ror r12, 63
	or r12, rax
	and r12, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+10]
	movzx r9d, BYTE PTR [rdi+11]
	ror r9, 56
	or r8, r9
	add r13, r8
	add r13, r10
	and r13, 65535
	mov rax, r13
	shr rax, 14
	ror r13, 62
	or r13, rax
	and r13, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+12]
	movzx r9d, BYTE PTR [rdi+13]
	ror r9, 56
	or r8, r9
	add r14, r8
	add r14, r10
	and r14, 65535
	mov rax, r14
	shr rax, 13
	ror r14, 61
	or r14, rax
	and r14, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+14]
	movzx r9d, BYTE PTR [rdi+15]
	ror r9, 56
	or r8, r9
	add r15, r8
	add r15, r10
	and r15, 65535
	mov rax, r15
	shr rax, 11
	ror r15, 59
	or r15, rax
	and r15, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+16]
	movzx r9d, BYTE PTR [rdi+17]
	ror r9, 56
	or r8, r9
	add r12, r8
	add r12, r10
	and r12, 65535
	mov rax, r12
	shr rax, 15
	ror r12, 63
	or r12, rax
	and r12, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+18]
	movzx r9d, BYTE PTR [rdi+19]
	ror r9, 56
	or r8, r9
	add r13, r8
	add r13, r10
	and r13, 65535
	mov rax, r13
	shr rax, 14
	ror r13, 62
	or r13, rax
	and r13, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+20]
	movzx r9d, BYTE PTR [rdi+21]
	ror r9, 56
	or r8, r9
	add r14, r8
	add r14, r10
	and r14, 65535
	mov rax, r14
	shr rax, 13
	ror r14, 61
	or r14, rax
	and r14, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+22]
	movzx r9d, BYTE PTR [rdi+23]
	ror r9, 56
	or r8, r9
	add r15, r8
	add r15, r10
	and r15, 65535
	mov rax, r15
	shr rax, 11
	ror r15, 59
	or r15, rax
	and r15, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+24]
	movzx r9d, BYTE PTR [rdi+25]
	ror r9, 56
	or r8, r9
	add r12, r8
	add r12, r10
	and r12, 65535
	mov rax, r12
	shr rax, 15
	ror r12, 63
	or r12, rax
	and r12, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+26]
	movzx r9d, BYTE PTR [rdi+27]
	ror r9, 56
	or r8, r9
	add r13, r8
	add r13, r10
	and r13, 65535
	mov rax, r13
	shr rax, 14
	ror r13, 62
	or r13, rax
	and r13, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+28]
	movzx r9d, BYTE PTR [rdi+29]
	ror r9, 56
	or r8, r9
	add r14, r8
	add r14, r10
	and r14, 65535
	mov rax, r14
	shr rax, 13
	ror r14, 61
	or r14, rax
	and r14, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+30]
	movzx r9d, BYTE PTR [rdi+31]
	ror r9, 56
	or r8, r9
	add r15, r8
	add r15, r10
	and r15, 65535
	mov rax, r15
	shr rax, 11
	ror r15, 59
	or r15, rax
	and r15, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+32]
	movzx r9d, BYTE PTR [rdi+33]
	ror r9, 56
	or r8, r9
	add r12, r8
	add r12, r10
	and r12, 65535
	mov rax, r12
	shr rax, 15
	ror r12, 63
	or r12, rax
	and r12, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+34]
	movzx r9d, BYTE PTR [rdi+35]
	ror r9, 56
	or r8, r9
	add r13, r8
	add r13, r10
	and r13, 65535
	mov rax, r13
	shr rax, 14
	ror r13, 62
	or r13, rax
	and r13, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+36]
	movzx r9d, BYTE PTR [rdi+37]
	ror r9, 56
	or r8, r9
	add r14, r8
	add r14, r10
	and r14, 65535
	mov rax, r14
	shr rax, 13
	ror r14, 61
	or r14, rax
	and r14, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+38]
	movzx r9d, BYTE PTR [rdi+39]
	ror r9, 56
	or r8, r9
	add r15, r8
	add r15, r10
	and r15, 65535
	mov rax, r15
	shr rax, 11
	ror r15, 59
	or r15, rax
	and r15, 65535
	mov rax, r15
	and rax, 63
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movdqu xmm4, XMMWORD PTR [rdi]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+16]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+32]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+64]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+80]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+96]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+112]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	add r12, rax
	and r12, 65535
	mov rax, r12
	and rax, 63
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movdqu xmm4, XMMWORD PTR [rdi]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+16]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+32]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+64]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+80]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+96]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+112]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	add r13, rax
	and r13, 65535
	mov rax, r13
	and rax, 63
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movdqu xmm4, XMMWORD PTR [rdi]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+16]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+32]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+64]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+80]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+96]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+112]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	add r14, rax
	and r14, 65535
	mov rax, r14
	and rax, 63
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movdqu xmm4, XMMWORD PTR [rdi]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+16]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+32]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+64]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+80]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+96]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+112]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	add r15, rax
	and r15, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+40]
	movzx r9d, BYTE PTR [rdi+41]
	ror r9, 56
	or r8, r9
	add r12, r8
	add r12, r10
	and r12, 65535
	mov rax, r12
	shr rax, 15
	ror r12, 63
	or r12, rax
	and r12, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+42]
	movzx r9d, BYTE PTR [rdi+43]
	ror r9, 56
	or r8, r9
	add r13, r8
	add r13, r10
	and r13, 65535
	mov rax, r13
	shr rax, 14
	ror r13, 62
	or r13, rax
	and r13, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+44]
	movzx r9d, BYTE PTR [rdi+45]
	ror r9, 56
	or r8, r9
	add r14, r8
	add r14, r10
	and r14, 65535
	mov rax, r14
	shr rax, 13
	ror r14, 61
	or r14, rax
	and r14, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+46]
	movzx r9d, BYTE PTR [rdi+47]
	ror r9, 56
	or r8, r9
	add r15, r8
	add r15, r10
	and r15, 65535
	mov rax, r15
	shr rax, 11
	ror r15, 59
	or r15, rax
	and r15, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+48]
	movzx r9d, BYTE PTR [rdi+49]
	ror r9, 56
	or r8, r9
	add r12, r8
	add r12, r10
	and r12, 65535
	mov rax, r12
	shr rax, 15
	ror r12, 63
	or r12, rax
	and r12, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+50]
	movzx r9d, BYTE PTR [rdi+51]
	ror r9, 56
	or r8, r9
	add r13, r8
	add r13, r10
	and r13, 65535
	mov rax, r13
	shr rax, 14
	ror r13, 62
	or r13, rax
	and r13, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+52]
	movzx r9d, BYTE PTR [rdi+53]
	ror r9, 56
	or r8, r9
	add r14, r8
	add r14, r10
	and r14, 65535
	mov rax, r14
	shr rax, 13
	ror r14, 61
	or r14, rax
	and r14, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+54]
	movzx r9d, BYTE PTR [rdi+55]
	ror r9, 56
	or r8, r9
	add r15, r8
	add r15, r10
	and r15, 65535
	mov rax, r15
	shr rax, 11
	ror r15, 59
	or r15, rax
	and r15, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+56]
	movzx r9d, BYTE PTR [rdi+57]
	ror r9, 56
	or r8, r9
	add r12, r8
	add r12, r10
	and r12, 65535
	mov rax, r12
	shr rax, 15
	ror r12, 63
	or r12, rax
	and r12, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+58]
	movzx r9d, BYTE PTR [rdi+59]
	ror r9, 56
	or r8, r9
	add r13, r8
	add r13, r10
	and r13, 65535
	mov rax, r13
	shr rax, 14
	ror r13, 62
	or r13, rax
	and r13, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+60]
	movzx r9d, BYTE PTR [rdi+61]
	ror r9, 56
	or r8, r9
	add r14, r8
	add r14, r10
	and r14, 65535
	mov rax, r14
	shr rax, 13
	ror r14, 61
	or r14, rax
	and r14, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+62]
	movzx r9d, BYTE PTR [rdi+63]
	ror r9, 56
	or r8, r9
	add r15, r8
	add r15, r10
	and r15, 65535
	mov rax, r15
	shr rax, 11
	ror r15, 59
	or r15, rax
	and r15, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+64]
	movzx r9d, BYTE PTR [rdi+65]
	ror r9, 56
	or r8, r9
	add r12, r8
	add r12, r10
	and r12, 65535
	mov rax, r12
	shr rax, 15
	ror r12, 63
	or r12, rax
	and r12, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+66]
	movzx r9d, BYTE PTR [rdi+67]
	ror r9, 56
	or r8, r9
	add r13, r8
	add r13, r10
	and r13, 65535
	mov rax, r13
	shr rax, 14
	ror r13, 62
	or r13, rax
	and r13, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+68]
	movzx r9d, BYTE PTR [rdi+69]
	ror r9, 56
	or r8, r9
	add r14, r8
	add r14, r10
	and r14, 65535
	mov rax, r14
	shr rax, 13
	ror r14, 61
	or r14, rax
	and r14, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+70]
	movzx r9d, BYTE PTR [rdi+71]
	ror r9, 56
	or r8, r9
	add r15, r8
	add r15, r10
	and r15, 65535
	mov rax, r15
	shr rax, 11
	ror r15, 59
	or r15, rax
	and r15, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+72]
	movzx r9d, BYTE PTR [rdi+73]
	ror r9, 56
	or r8, r9
	add r12, r8
	add r12, r10
	and r12, 65535
	mov rax, r12
	shr rax, 15
	ror r12, 63
	or r12, rax
	and r12, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+74]
	movzx r9d, BYTE PTR [rdi+75]
	ror r9, 56
	or r8, r9
	add r13, r8
	add r13, r10
	and r13, 65535
	mov rax, r13
	shr rax, 14
	ror r13, 62
	or r13, rax
	and r13, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+76]
	movzx r9d, BYTE PTR [rdi+77]
	ror r9, 56
	or r8, r9
	add r14, r8
	add r14, r10
	and r14, 65535
	mov rax, r14
	shr rax, 13
	ror r14, 61
	or r14, rax
	and r14, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+78]
	movzx r9d, BYTE PTR [rdi+79]
	ror r9, 56
	or r8, r9
	add r15, r8
	add r15, r10
	and r15, 65535
	mov rax, r15
	shr rax, 11
	ror r15, 59
	or r15, rax
	and r15, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+80]
	movzx r9d, BYTE PTR [rdi+81]
	ror r9, 56
	or r8, r9
	add r12, r8
	add r12, r10
	and r12, 65535
	mov rax, r12
	shr rax, 15
	ror r12, 63
	or r12, rax
	and r12, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+82]
	movzx r9d, BYTE PTR [rdi+83]
	ror r9, 56
	or r8, r9
	add r13, r8
	add r13, r10
	and r13, 65535
	mov rax, r13
	shr rax, 14
	ror r13, 62
	or r13, rax
	and r13, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+84]
	movzx r9d, BYTE PTR [rdi+85]
	ror r9, 56
	or r8, r9
	add r14, r8
	add r14, r10
	and r14, 65535
	mov rax, r14
	shr rax, 13
	ror r14, 61
	or r14, rax
	and r14, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+86]
	movzx r9d, BYTE PTR [rdi+87]
	ror r9, 56
	or r8, r9
	add r15, r8
	add r15, r10
	and r15, 65535
	mov rax, r15
	shr rax, 11
	ror r15, 59
	or r15, rax
	and r15, 65535
	mov rax, r15
	and rax, 63
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movdqu xmm4, XMMWORD PTR [rdi]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+16]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+32]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+64]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+80]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+96]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+112]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	add r12, rax
	and r12, 65535
	mov rax, r12
	and rax, 63
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movdqu xmm4, XMMWORD PTR [rdi]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+16]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+32]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+64]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+80]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+96]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+112]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	add r13, rax
	and r13, 65535
	mov rax, r13
	and rax, 63
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movdqu xmm4, XMMWORD PTR [rdi]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+16]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+32]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+64]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+80]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+96]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+112]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	add r14, rax
	and r14, 65535
	mov rax, r14
	and rax, 63
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movdqu xmm4, XMMWORD PTR [rdi]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+16]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+32]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+64]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+80]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+96]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+112]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	add r15, rax
	and r15, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+88]
	movzx r9d, BYTE PTR [rdi+89]
	ror r9, 56
	or r8, r9
	add r12, r8
	add r12, r10
	and r12, 65535
	mov rax, r12
	shr rax, 15
	ror r12, 63
	or r12, rax
	and r12, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+90]
	movzx r9d, BYTE PTR [rdi+91]
	ror r9, 56
	or r8, r9
	add r13, r8
	add r13, r10
	and r13, 65535
	mov rax, r13
	shr rax, 14
	ror r13, 62
	or r13, rax
	and r13, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+92]
	movzx r9d, BYTE PTR [rdi+93]
	ror r9, 56
	or r8, r9
	add r14, r8
	add r14, r10
	and r14, 65535
	mov rax, r14
	shr rax, 13
	ror r14, 61
	or r14, rax
	and r14, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+94]
	movzx r9d, BYTE PTR [rdi+95]
	ror r9, 56
	or r8, r9
	add r15, r8
	add r15, r10
	and r15, 65535
	mov rax, r15
	shr rax, 11
	ror r15, 59
	or r15, rax
	and r15, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+96]
	movzx r9d, BYTE PTR [rdi+97]
	ror r9, 56
	or r8, r9
	add r12, r8
	add r12, r10
	and r12, 65535
	mov rax, r12
	shr rax, 15
	ror r12, 63
	or r12, rax
	and r12, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+98]
	movzx r9d, BYTE PTR [rdi+99]
	ror r9, 56
	or r8, r9
	add r13, r8
	add r13, r10
	and r13, 65535
	mov rax, r13
	shr rax, 14
	ror r13, 62
	or r13, rax
	and r13, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+100]
	movzx r9d, BYTE PTR [rdi+101]
	ror r9, 56
	or r8, r9
	add r14, r8
	add r14, r10
	and r14, 65535
	mov rax, r14
	shr rax, 13
	ror r14, 61
	or r14, rax
	and r14, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+102]
	movzx r9d, BYTE PTR [rdi+103]
	ror r9, 56
	or r8, r9
	add r15, r8
	add r15, r10
	and r15, 65535
	mov rax, r15
	shr rax, 11
	ror r15, 59
	or r15, rax
	and r15, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+104]
	movzx r9d, BYTE PTR [rdi+105]
	ror r9, 56
	or r8, r9
	add r12, r8
	add r12, r10
	and r12, 65535
	mov rax, r12
	shr rax, 15
	ror r12, 63
	or r12, rax
	and r12, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+106]
	movzx r9d, BYTE PTR [rdi+107]
	ror r9, 56
	or r8, r9
	add r13, r8
	add r13, r10
	and r13, 65535
	mov rax, r13
	shr rax, 14
	ror r13, 62
	or r13, rax
	and r13, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+108]
	movzx r9d, BYTE PTR [rdi+109]
	ror r9, 56
	or r8, r9
	add r14, r8
	add r14, r10
	and r14, 65535
	mov rax, r14
	shr rax, 13
	ror r14, 61
	or r14, rax
	and r14, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+110]
	movzx r9d, BYTE PTR [rdi+111]
	ror r9, 56
	or r8, r9
	add r15, r8
	add r15, r10
	and r15, 65535
	mov rax, r15
	shr rax, 11
	ror r15, 59
	or r15, rax
	and r15, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+112]
	movzx r9d, BYTE PTR [rdi+113]
	ror r9, 56
	or r8, r9
	add r12, r8
	add r12, r10
	and r12, 65535
	mov rax, r12
	shr rax, 15
	ror r12, 63
	or r12, rax
	and r12, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+114]
	movzx r9d, BYTE PTR [rdi+115]
	ror r9, 56
	or r8, r9
	add r13, r8
	add r13, r10
	and r13, 65535
	mov rax, r13
	shr rax, 14
	ror r13, 62
	or r13, rax
	and r13, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+116]
	movzx r9d, BYTE PTR [rdi+117]
	ror r9, 56
	or r8, r9
	add r14, r8
	add r14, r10
	and r14, 65535
	mov rax, r14
	shr rax, 13
	ror r14, 61
	or r14, rax
	and r14, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+118]
	movzx r9d, BYTE PTR [rdi+119]
	ror r9, 56
	or r8, r9
	add r15, r8
	add r15, r10
	and r15, 65535
	mov rax, r15
	shr rax, 11
	ror r15, 59
	or r15, rax
	and r15, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+120]
	movzx r9d, BYTE PTR [rdi+121]
	ror r9, 56
	or r8, r9
	add r12, r8
	add r12, r10
	and r12, 65535
	mov rax, r12
	shr rax, 15
	ror r12, 63
	or r12, rax
	and r12, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+122]
	movzx r9d, BYTE PTR [rdi+123]
	ror r9, 56
	or r8, r9
	add r13, r8
	add r13, r10
	and r13, 65535
	mov rax, r13
	shr rax, 14
	ror r13, 62
	or r13, rax
	and r13, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+124]
	movzx r9d, BYTE PTR [rdi+125]
	ror r9, 56
	or r8, r9
	add r14, r8
	add r14, r10
	and r14, 65535
	mov rax, r14
	shr rax, 13
	ror r14, 61
	or r14, rax
	and r14, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+126]
	movzx r9d, BYTE PTR [rdi+127]
	ror r9, 56
	or r8, r9
	add r15, r8
	add r15, r10
	and r15, 65535
	mov rax, r15
	shr rax, 11
	ror r15, 59
	or r15, rax
	and r15, 65535
	mov rax, r12
	mov rcx, r13
	ror rcx, 48
	or rax, rcx
	mov rcx, r14
	ror rcx, 32
	or rax, rcx
	mov rcx, r15
	ror rcx, 16
	or rax, rcx
	mov QWORD PTR [rsi], rax
	mov r12, QWORD PTR [rdx]
	mov r13, QWORD PTR [rdx+8]
	mov r14, QWORD PTR [rdx+16]
	mov r15, QWORD PTR [rdx+24]
	ret
	.p2align 6

vg_rc2_decrypt_block:
	mov QWORD PTR [rdx], r12
	mov QWORD PTR [rdx+8], r13
	mov QWORD PTR [rdx+16], r14
	mov QWORD PTR [rdx+24], r15
	mov rax, QWORD PTR [rsi]
	mov r12, rax
	and r12, 65535
	mov r13, rax
	shr r13, 16
	and r13, 65535
	mov r14, rax
	shr r14, 32
	and r14, 65535
	mov r15, rax
	shr r15, 48
	and r15, 65535
	mov rax, r15
	shr rax, 5
	ror r15, 53
	or r15, rax
	and r15, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+126]
	movzx r9d, BYTE PTR [rdi+127]
	ror r9, 56
	or r8, r9
	sub r15, r8
	sub r15, r10
	and r15, 65535
	mov rax, r14
	shr rax, 3
	ror r14, 51
	or r14, rax
	and r14, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+124]
	movzx r9d, BYTE PTR [rdi+125]
	ror r9, 56
	or r8, r9
	sub r14, r8
	sub r14, r10
	and r14, 65535
	mov rax, r13
	shr rax, 2
	ror r13, 50
	or r13, rax
	and r13, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+122]
	movzx r9d, BYTE PTR [rdi+123]
	ror r9, 56
	or r8, r9
	sub r13, r8
	sub r13, r10
	and r13, 65535
	mov rax, r12
	shr rax, 1
	ror r12, 49
	or r12, rax
	and r12, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+120]
	movzx r9d, BYTE PTR [rdi+121]
	ror r9, 56
	or r8, r9
	sub r12, r8
	sub r12, r10
	and r12, 65535
	mov rax, r15
	shr rax, 5
	ror r15, 53
	or r15, rax
	and r15, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+118]
	movzx r9d, BYTE PTR [rdi+119]
	ror r9, 56
	or r8, r9
	sub r15, r8
	sub r15, r10
	and r15, 65535
	mov rax, r14
	shr rax, 3
	ror r14, 51
	or r14, rax
	and r14, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+116]
	movzx r9d, BYTE PTR [rdi+117]
	ror r9, 56
	or r8, r9
	sub r14, r8
	sub r14, r10
	and r14, 65535
	mov rax, r13
	shr rax, 2
	ror r13, 50
	or r13, rax
	and r13, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+114]
	movzx r9d, BYTE PTR [rdi+115]
	ror r9, 56
	or r8, r9
	sub r13, r8
	sub r13, r10
	and r13, 65535
	mov rax, r12
	shr rax, 1
	ror r12, 49
	or r12, rax
	and r12, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+112]
	movzx r9d, BYTE PTR [rdi+113]
	ror r9, 56
	or r8, r9
	sub r12, r8
	sub r12, r10
	and r12, 65535
	mov rax, r15
	shr rax, 5
	ror r15, 53
	or r15, rax
	and r15, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+110]
	movzx r9d, BYTE PTR [rdi+111]
	ror r9, 56
	or r8, r9
	sub r15, r8
	sub r15, r10
	and r15, 65535
	mov rax, r14
	shr rax, 3
	ror r14, 51
	or r14, rax
	and r14, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+108]
	movzx r9d, BYTE PTR [rdi+109]
	ror r9, 56
	or r8, r9
	sub r14, r8
	sub r14, r10
	and r14, 65535
	mov rax, r13
	shr rax, 2
	ror r13, 50
	or r13, rax
	and r13, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+106]
	movzx r9d, BYTE PTR [rdi+107]
	ror r9, 56
	or r8, r9
	sub r13, r8
	sub r13, r10
	and r13, 65535
	mov rax, r12
	shr rax, 1
	ror r12, 49
	or r12, rax
	and r12, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+104]
	movzx r9d, BYTE PTR [rdi+105]
	ror r9, 56
	or r8, r9
	sub r12, r8
	sub r12, r10
	and r12, 65535
	mov rax, r15
	shr rax, 5
	ror r15, 53
	or r15, rax
	and r15, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+102]
	movzx r9d, BYTE PTR [rdi+103]
	ror r9, 56
	or r8, r9
	sub r15, r8
	sub r15, r10
	and r15, 65535
	mov rax, r14
	shr rax, 3
	ror r14, 51
	or r14, rax
	and r14, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+100]
	movzx r9d, BYTE PTR [rdi+101]
	ror r9, 56
	or r8, r9
	sub r14, r8
	sub r14, r10
	and r14, 65535
	mov rax, r13
	shr rax, 2
	ror r13, 50
	or r13, rax
	and r13, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+98]
	movzx r9d, BYTE PTR [rdi+99]
	ror r9, 56
	or r8, r9
	sub r13, r8
	sub r13, r10
	and r13, 65535
	mov rax, r12
	shr rax, 1
	ror r12, 49
	or r12, rax
	and r12, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+96]
	movzx r9d, BYTE PTR [rdi+97]
	ror r9, 56
	or r8, r9
	sub r12, r8
	sub r12, r10
	and r12, 65535
	mov rax, r15
	shr rax, 5
	ror r15, 53
	or r15, rax
	and r15, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+94]
	movzx r9d, BYTE PTR [rdi+95]
	ror r9, 56
	or r8, r9
	sub r15, r8
	sub r15, r10
	and r15, 65535
	mov rax, r14
	shr rax, 3
	ror r14, 51
	or r14, rax
	and r14, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+92]
	movzx r9d, BYTE PTR [rdi+93]
	ror r9, 56
	or r8, r9
	sub r14, r8
	sub r14, r10
	and r14, 65535
	mov rax, r13
	shr rax, 2
	ror r13, 50
	or r13, rax
	and r13, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+90]
	movzx r9d, BYTE PTR [rdi+91]
	ror r9, 56
	or r8, r9
	sub r13, r8
	sub r13, r10
	and r13, 65535
	mov rax, r12
	shr rax, 1
	ror r12, 49
	or r12, rax
	and r12, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+88]
	movzx r9d, BYTE PTR [rdi+89]
	ror r9, 56
	or r8, r9
	sub r12, r8
	sub r12, r10
	and r12, 65535
	mov rax, r14
	and rax, 63
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movdqu xmm4, XMMWORD PTR [rdi]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+16]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+32]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+64]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+80]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+96]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+112]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	sub r15, rax
	and r15, 65535
	mov rax, r13
	and rax, 63
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movdqu xmm4, XMMWORD PTR [rdi]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+16]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+32]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+64]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+80]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+96]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+112]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	sub r14, rax
	and r14, 65535
	mov rax, r12
	and rax, 63
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movdqu xmm4, XMMWORD PTR [rdi]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+16]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+32]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+64]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+80]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+96]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+112]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	sub r13, rax
	and r13, 65535
	mov rax, r15
	and rax, 63
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movdqu xmm4, XMMWORD PTR [rdi]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+16]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+32]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+64]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+80]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+96]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+112]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	sub r12, rax
	and r12, 65535
	mov rax, r15
	shr rax, 5
	ror r15, 53
	or r15, rax
	and r15, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+86]
	movzx r9d, BYTE PTR [rdi+87]
	ror r9, 56
	or r8, r9
	sub r15, r8
	sub r15, r10
	and r15, 65535
	mov rax, r14
	shr rax, 3
	ror r14, 51
	or r14, rax
	and r14, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+84]
	movzx r9d, BYTE PTR [rdi+85]
	ror r9, 56
	or r8, r9
	sub r14, r8
	sub r14, r10
	and r14, 65535
	mov rax, r13
	shr rax, 2
	ror r13, 50
	or r13, rax
	and r13, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+82]
	movzx r9d, BYTE PTR [rdi+83]
	ror r9, 56
	or r8, r9
	sub r13, r8
	sub r13, r10
	and r13, 65535
	mov rax, r12
	shr rax, 1
	ror r12, 49
	or r12, rax
	and r12, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+80]
	movzx r9d, BYTE PTR [rdi+81]
	ror r9, 56
	or r8, r9
	sub r12, r8
	sub r12, r10
	and r12, 65535
	mov rax, r15
	shr rax, 5
	ror r15, 53
	or r15, rax
	and r15, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+78]
	movzx r9d, BYTE PTR [rdi+79]
	ror r9, 56
	or r8, r9
	sub r15, r8
	sub r15, r10
	and r15, 65535
	mov rax, r14
	shr rax, 3
	ror r14, 51
	or r14, rax
	and r14, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+76]
	movzx r9d, BYTE PTR [rdi+77]
	ror r9, 56
	or r8, r9
	sub r14, r8
	sub r14, r10
	and r14, 65535
	mov rax, r13
	shr rax, 2
	ror r13, 50
	or r13, rax
	and r13, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+74]
	movzx r9d, BYTE PTR [rdi+75]
	ror r9, 56
	or r8, r9
	sub r13, r8
	sub r13, r10
	and r13, 65535
	mov rax, r12
	shr rax, 1
	ror r12, 49
	or r12, rax
	and r12, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+72]
	movzx r9d, BYTE PTR [rdi+73]
	ror r9, 56
	or r8, r9
	sub r12, r8
	sub r12, r10
	and r12, 65535
	mov rax, r15
	shr rax, 5
	ror r15, 53
	or r15, rax
	and r15, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+70]
	movzx r9d, BYTE PTR [rdi+71]
	ror r9, 56
	or r8, r9
	sub r15, r8
	sub r15, r10
	and r15, 65535
	mov rax, r14
	shr rax, 3
	ror r14, 51
	or r14, rax
	and r14, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+68]
	movzx r9d, BYTE PTR [rdi+69]
	ror r9, 56
	or r8, r9
	sub r14, r8
	sub r14, r10
	and r14, 65535
	mov rax, r13
	shr rax, 2
	ror r13, 50
	or r13, rax
	and r13, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+66]
	movzx r9d, BYTE PTR [rdi+67]
	ror r9, 56
	or r8, r9
	sub r13, r8
	sub r13, r10
	and r13, 65535
	mov rax, r12
	shr rax, 1
	ror r12, 49
	or r12, rax
	and r12, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+64]
	movzx r9d, BYTE PTR [rdi+65]
	ror r9, 56
	or r8, r9
	sub r12, r8
	sub r12, r10
	and r12, 65535
	mov rax, r15
	shr rax, 5
	ror r15, 53
	or r15, rax
	and r15, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+62]
	movzx r9d, BYTE PTR [rdi+63]
	ror r9, 56
	or r8, r9
	sub r15, r8
	sub r15, r10
	and r15, 65535
	mov rax, r14
	shr rax, 3
	ror r14, 51
	or r14, rax
	and r14, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+60]
	movzx r9d, BYTE PTR [rdi+61]
	ror r9, 56
	or r8, r9
	sub r14, r8
	sub r14, r10
	and r14, 65535
	mov rax, r13
	shr rax, 2
	ror r13, 50
	or r13, rax
	and r13, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+58]
	movzx r9d, BYTE PTR [rdi+59]
	ror r9, 56
	or r8, r9
	sub r13, r8
	sub r13, r10
	and r13, 65535
	mov rax, r12
	shr rax, 1
	ror r12, 49
	or r12, rax
	and r12, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+56]
	movzx r9d, BYTE PTR [rdi+57]
	ror r9, 56
	or r8, r9
	sub r12, r8
	sub r12, r10
	and r12, 65535
	mov rax, r15
	shr rax, 5
	ror r15, 53
	or r15, rax
	and r15, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+54]
	movzx r9d, BYTE PTR [rdi+55]
	ror r9, 56
	or r8, r9
	sub r15, r8
	sub r15, r10
	and r15, 65535
	mov rax, r14
	shr rax, 3
	ror r14, 51
	or r14, rax
	and r14, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+52]
	movzx r9d, BYTE PTR [rdi+53]
	ror r9, 56
	or r8, r9
	sub r14, r8
	sub r14, r10
	and r14, 65535
	mov rax, r13
	shr rax, 2
	ror r13, 50
	or r13, rax
	and r13, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+50]
	movzx r9d, BYTE PTR [rdi+51]
	ror r9, 56
	or r8, r9
	sub r13, r8
	sub r13, r10
	and r13, 65535
	mov rax, r12
	shr rax, 1
	ror r12, 49
	or r12, rax
	and r12, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+48]
	movzx r9d, BYTE PTR [rdi+49]
	ror r9, 56
	or r8, r9
	sub r12, r8
	sub r12, r10
	and r12, 65535
	mov rax, r15
	shr rax, 5
	ror r15, 53
	or r15, rax
	and r15, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+46]
	movzx r9d, BYTE PTR [rdi+47]
	ror r9, 56
	or r8, r9
	sub r15, r8
	sub r15, r10
	and r15, 65535
	mov rax, r14
	shr rax, 3
	ror r14, 51
	or r14, rax
	and r14, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+44]
	movzx r9d, BYTE PTR [rdi+45]
	ror r9, 56
	or r8, r9
	sub r14, r8
	sub r14, r10
	and r14, 65535
	mov rax, r13
	shr rax, 2
	ror r13, 50
	or r13, rax
	and r13, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+42]
	movzx r9d, BYTE PTR [rdi+43]
	ror r9, 56
	or r8, r9
	sub r13, r8
	sub r13, r10
	and r13, 65535
	mov rax, r12
	shr rax, 1
	ror r12, 49
	or r12, rax
	and r12, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+40]
	movzx r9d, BYTE PTR [rdi+41]
	ror r9, 56
	or r8, r9
	sub r12, r8
	sub r12, r10
	and r12, 65535
	mov rax, r14
	and rax, 63
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movdqu xmm4, XMMWORD PTR [rdi]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+16]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+32]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+64]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+80]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+96]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+112]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	sub r15, rax
	and r15, 65535
	mov rax, r13
	and rax, 63
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movdqu xmm4, XMMWORD PTR [rdi]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+16]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+32]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+64]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+80]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+96]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+112]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	sub r14, rax
	and r14, 65535
	mov rax, r12
	and rax, 63
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movdqu xmm4, XMMWORD PTR [rdi]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+16]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+32]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+64]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+80]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+96]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+112]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	sub r13, rax
	and r13, 65535
	mov rax, r15
	and rax, 63
	movq xmm0, rax
	punpcklwd xmm0, xmm0
	pshufd xmm0, xmm0, 0
	pxor xmm1, xmm1
	movabs r10, 844433520132096
	movq xmm2, r10
	movabs r10, 1970350607106052
	movq xmm5, r10
	punpcklqdq xmm2, xmm5
	movabs r10, 281479271743489
	movq xmm6, r10
	movabs r10, 281479271743489
	movq xmm5, r10
	punpcklqdq xmm6, xmm5
	movabs r10, 2251834173947912
	movq xmm7, r10
	movabs r10, 2251834173947912
	movq xmm5, r10
	punpcklqdq xmm7, xmm5
	movdqu xmm4, XMMWORD PTR [rdi]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+16]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+32]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+64]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+80]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+96]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [rdi+112]
	movdqa xmm3, xmm0
	pxor xmm3, xmm2
	psubw xmm3, xmm6
	psraw xmm3, 15
	pand xmm3, xmm4
	por xmm1, xmm3
	paddw xmm2, xmm7
	movdqa xmm3, xmm1
	psrldq xmm3, 8
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 4
	por xmm1, xmm3
	movdqa xmm3, xmm1
	psrldq xmm3, 2
	por xmm1, xmm3
	movq rax, xmm1
	and rax, 65535
	sub r12, rax
	and r12, 65535
	mov rax, r15
	shr rax, 5
	ror r15, 53
	or r15, rax
	and r15, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+38]
	movzx r9d, BYTE PTR [rdi+39]
	ror r9, 56
	or r8, r9
	sub r15, r8
	sub r15, r10
	and r15, 65535
	mov rax, r14
	shr rax, 3
	ror r14, 51
	or r14, rax
	and r14, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+36]
	movzx r9d, BYTE PTR [rdi+37]
	ror r9, 56
	or r8, r9
	sub r14, r8
	sub r14, r10
	and r14, 65535
	mov rax, r13
	shr rax, 2
	ror r13, 50
	or r13, rax
	and r13, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+34]
	movzx r9d, BYTE PTR [rdi+35]
	ror r9, 56
	or r8, r9
	sub r13, r8
	sub r13, r10
	and r13, 65535
	mov rax, r12
	shr rax, 1
	ror r12, 49
	or r12, rax
	and r12, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+32]
	movzx r9d, BYTE PTR [rdi+33]
	ror r9, 56
	or r8, r9
	sub r12, r8
	sub r12, r10
	and r12, 65535
	mov rax, r15
	shr rax, 5
	ror r15, 53
	or r15, rax
	and r15, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+30]
	movzx r9d, BYTE PTR [rdi+31]
	ror r9, 56
	or r8, r9
	sub r15, r8
	sub r15, r10
	and r15, 65535
	mov rax, r14
	shr rax, 3
	ror r14, 51
	or r14, rax
	and r14, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+28]
	movzx r9d, BYTE PTR [rdi+29]
	ror r9, 56
	or r8, r9
	sub r14, r8
	sub r14, r10
	and r14, 65535
	mov rax, r13
	shr rax, 2
	ror r13, 50
	or r13, rax
	and r13, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+26]
	movzx r9d, BYTE PTR [rdi+27]
	ror r9, 56
	or r8, r9
	sub r13, r8
	sub r13, r10
	and r13, 65535
	mov rax, r12
	shr rax, 1
	ror r12, 49
	or r12, rax
	and r12, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+24]
	movzx r9d, BYTE PTR [rdi+25]
	ror r9, 56
	or r8, r9
	sub r12, r8
	sub r12, r10
	and r12, 65535
	mov rax, r15
	shr rax, 5
	ror r15, 53
	or r15, rax
	and r15, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+22]
	movzx r9d, BYTE PTR [rdi+23]
	ror r9, 56
	or r8, r9
	sub r15, r8
	sub r15, r10
	and r15, 65535
	mov rax, r14
	shr rax, 3
	ror r14, 51
	or r14, rax
	and r14, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+20]
	movzx r9d, BYTE PTR [rdi+21]
	ror r9, 56
	or r8, r9
	sub r14, r8
	sub r14, r10
	and r14, 65535
	mov rax, r13
	shr rax, 2
	ror r13, 50
	or r13, rax
	and r13, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+18]
	movzx r9d, BYTE PTR [rdi+19]
	ror r9, 56
	or r8, r9
	sub r13, r8
	sub r13, r10
	and r13, 65535
	mov rax, r12
	shr rax, 1
	ror r12, 49
	or r12, rax
	and r12, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+16]
	movzx r9d, BYTE PTR [rdi+17]
	ror r9, 56
	or r8, r9
	sub r12, r8
	sub r12, r10
	and r12, 65535
	mov rax, r15
	shr rax, 5
	ror r15, 53
	or r15, rax
	and r15, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+14]
	movzx r9d, BYTE PTR [rdi+15]
	ror r9, 56
	or r8, r9
	sub r15, r8
	sub r15, r10
	and r15, 65535
	mov rax, r14
	shr rax, 3
	ror r14, 51
	or r14, rax
	and r14, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+12]
	movzx r9d, BYTE PTR [rdi+13]
	ror r9, 56
	or r8, r9
	sub r14, r8
	sub r14, r10
	and r14, 65535
	mov rax, r13
	shr rax, 2
	ror r13, 50
	or r13, rax
	and r13, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+10]
	movzx r9d, BYTE PTR [rdi+11]
	ror r9, 56
	or r8, r9
	sub r13, r8
	sub r13, r10
	and r13, 65535
	mov rax, r12
	shr rax, 1
	ror r12, 49
	or r12, rax
	and r12, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi+8]
	movzx r9d, BYTE PTR [rdi+9]
	ror r9, 56
	or r8, r9
	sub r12, r8
	sub r12, r10
	and r12, 65535
	mov rax, r15
	shr rax, 5
	ror r15, 53
	or r15, rax
	and r15, 65535
	mov r10, r14
	and r10, r13
	mov r11, r14
	xor r11, -1
	and r11, r12
	add r10, r11
	movzx r8d, BYTE PTR [rdi+6]
	movzx r9d, BYTE PTR [rdi+7]
	ror r9, 56
	or r8, r9
	sub r15, r8
	sub r15, r10
	and r15, 65535
	mov rax, r14
	shr rax, 3
	ror r14, 51
	or r14, rax
	and r14, 65535
	mov r10, r13
	and r10, r12
	mov r11, r13
	xor r11, -1
	and r11, r15
	add r10, r11
	movzx r8d, BYTE PTR [rdi+4]
	movzx r9d, BYTE PTR [rdi+5]
	ror r9, 56
	or r8, r9
	sub r14, r8
	sub r14, r10
	and r14, 65535
	mov rax, r13
	shr rax, 2
	ror r13, 50
	or r13, rax
	and r13, 65535
	mov r10, r12
	and r10, r15
	mov r11, r12
	xor r11, -1
	and r11, r14
	add r10, r11
	movzx r8d, BYTE PTR [rdi+2]
	movzx r9d, BYTE PTR [rdi+3]
	ror r9, 56
	or r8, r9
	sub r13, r8
	sub r13, r10
	and r13, 65535
	mov rax, r12
	shr rax, 1
	ror r12, 49
	or r12, rax
	and r12, 65535
	mov r10, r15
	and r10, r14
	mov r11, r15
	xor r11, -1
	and r11, r13
	add r10, r11
	movzx r8d, BYTE PTR [rdi]
	movzx r9d, BYTE PTR [rdi+1]
	ror r9, 56
	or r8, r9
	sub r12, r8
	sub r12, r10
	and r12, 65535
	mov rax, r12
	mov rcx, r13
	ror rcx, 48
	or rax, rcx
	mov rcx, r14
	ror rcx, 32
	or rax, rcx
	mov rcx, r15
	ror rcx, 16
	or rax, rcx
	mov QWORD PTR [rsi], rax
	mov r12, QWORD PTR [rdx]
	mov r13, QWORD PTR [rdx+8]
	mov r14, QWORD PTR [rdx+16]
	mov r15, QWORD PTR [rdx+24]
	ret
	.p2align 6
