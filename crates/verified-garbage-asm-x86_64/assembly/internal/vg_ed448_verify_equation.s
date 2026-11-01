// The functions of `src/internal/vg_ed448_verify_equation.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_verify_equation:
	mov QWORD PTR [rcx], rbx
	mov QWORD PTR [rcx+8], rbp
	mov QWORD PTR [rcx+16], r12
	mov QWORD PTR [rcx+24], r13
	mov QWORD PTR [rcx+32], r14
	mov QWORD PTR [rcx+40], r15
	mov r8, rdi
	mov r9, rsi
	mov rdi, rcx
	mov rsi, rdx
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rsi+rbx*1]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2560], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2561], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2562], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2563], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2564], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2565], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2566], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2567], dl
	add rbx, 1
	cmp rbx, 57
	jne 20b
	mov edx, 0
	mov BYTE PTR [rdi+2559], dl
	mov BYTE PTR [rdi+3016], dl
	mov BYTE PTR [rdi+3017], dl
	mov BYTE PTR [rdi+3018], dl
	mov BYTE PTR [rdi+3019], dl
	mov rsi, r9
	add rsi, 57
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rsi+rbx*1]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2048], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2049], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2050], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2051], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2052], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2053], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2054], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2055], dl
	add rbx, 1
	cmp rbx, 57
	jne 21b
	mov edx, 0
	mov BYTE PTR [rdi+2047], dl
	mov BYTE PTR [rdi+2504], dl
	mov BYTE PTR [rdi+2505], dl
	mov BYTE PTR [rdi+2506], dl
	mov BYTE PTR [rdi+2507], dl
	mov QWORD PTR [rdi+1664], r8
	mov QWORD PTR [rdi+1672], r9
	mov eax, 0
	mov QWORD PTR [rdi+1688], rax
	movabs r8, -2556006723728458995
	movabs r9, -2408513697996967766
	movabs r10, 4301259484579875183
	movabs r11, 2201345046
	movabs r12, 0
	movabs r13, 0
	movabs r14, -4611686018427387904
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	adc r12, QWORD PTR [rdi+160]
	adc r13, QWORD PTR [rdi+168]
	adc r14, QWORD PTR [rdi+176]
	mov edx, 0
	adc rdx, 0
	movzx eax, BYTE PTR [rsi+56]
	or rdx, rax
	mov rax, QWORD PTR [rdi+1688]
	or rax, rdx
	mov QWORD PTR [rdi+1688], rax
	mov rsi, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+1880], rsi
	mov ebx, 2
	mov QWORD PTR [rdi+1888], rbx
22:
	mov r8, QWORD PTR [rdi+448]
	mov r9, QWORD PTR [rdi+456]
	mov r10, QWORD PTR [rdi+464]
	mov r11, QWORD PTR [rdi+472]
	mov r12, QWORD PTR [rdi+480]
	mov r13, QWORD PTR [rdi+488]
	mov r14, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+1768], r8
	mov QWORD PTR [rdi+1776], r9
	mov QWORD PTR [rdi+1784], r10
	mov QWORD PTR [rdi+1792], r11
	mov QWORD PTR [rdi+1800], r12
	mov QWORD PTR [rdi+1808], r13
	mov QWORD PTR [rdi+1816], r14
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	mov r12, QWORD PTR [rdi+544]
	mov r13, QWORD PTR [rdi+552]
	mov r14, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+1824], r8
	mov QWORD PTR [rdi+1832], r9
	mov QWORD PTR [rdi+1840], r10
	mov QWORD PTR [rdi+1848], r11
	mov QWORD PTR [rdi+1856], r12
	mov QWORD PTR [rdi+1864], r13
	mov QWORD PTR [rdi+1872], r14
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	movabs r8, 2749069528532828254
	movabs r9, 4844607530355168142
	movabs r10, 1346042987506197777
	movabs r11, -1554336549866068892
	movabs r12, -7055903183279810713
	movabs r13, 2458144774905870042
	movabs r14, 5699710800930606573
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r14
	movabs r8, -7491604544318539244
	movabs r9, -162952930493216595
	movabs r10, 4239012173876836804
	movabs r11, -8685020228626627881
	movabs r12, 5470311636975982656
	movabs r13, -8613661815248140446
	movabs r14, 7583857750517922852
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov QWORD PTR [rdi+672], r12
	mov QWORD PTR [rdi+680], r13
	mov QWORD PTR [rdi+688], r14
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	mov QWORD PTR [rdi+736], r12
	mov QWORD PTR [rdi+744], r13
	mov QWORD PTR [rdi+752], r14
	movabs r8, -39082
	movabs r9, -1
	movabs r10, -1
	movabs r11, -4294967297
	movabs r12, -1
	movabs r13, -1
	movabs r14, -1
	mov QWORD PTR [rdi+768], r8
	mov QWORD PTR [rdi+776], r9
	mov QWORD PTR [rdi+784], r10
	mov QWORD PTR [rdi+792], r11
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov rsi, QWORD PTR [rdi+1880]
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov QWORD PTR [rdi+544], r12
	mov QWORD PTR [rdi+552], r13
	mov QWORD PTR [rdi+560], r14
	movzx edx, BYTE PTR [rsi+56]
	mov rax, rdx
	shr rax, 7
	mov QWORD PTR [rdi+1696], rax
	and rdx, 127
	mov rax, QWORD PTR [rdi+1688]
	or rax, rdx
	mov QWORD PTR [rdi+1688], rax
	mov r15d, 1
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	mov r12, QWORD PTR [rdi+544]
	mov r13, QWORD PTR [rdi+552]
	mov r14, QWORD PTR [rdi+560]
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	sbb r15, r15
	mov rax, QWORD PTR [rdi+512]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+520]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+528]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+536]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+544]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+552]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+560]
	xor r14, rax
	and r14, r15
	xor r14, rax
	mov edx, 0
	mov rax, QWORD PTR [rdi+512]
	xor rax, r8
	or rdx, rax
	mov rax, QWORD PTR [rdi+520]
	xor rax, r9
	or rdx, rax
	mov rax, QWORD PTR [rdi+528]
	xor rax, r10
	or rdx, rax
	mov rax, QWORD PTR [rdi+536]
	xor rax, r11
	or rdx, rax
	mov rax, QWORD PTR [rdi+544]
	xor rax, r12
	or rdx, rax
	mov rax, QWORD PTR [rdi+552]
	xor rax, r13
	or rdx, rax
	mov rax, QWORD PTR [rdi+560]
	xor rax, r14
	or rdx, rax
	mov rax, QWORD PTR [rdi+1688]
	or rax, rdx
	mov QWORD PTR [rdi+1688], rax
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	mov r12, QWORD PTR [rdi+544]
	mov r13, QWORD PTR [rdi+552]
	mov r14, QWORD PTR [rdi+560]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, r8
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, r8
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, r8
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, r8
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, r8
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r9
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, r8
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r10
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, r8
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r10
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r11
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, r9
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r11
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, r10
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r11
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r12
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, r11
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r12
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, r12
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r13
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, r13
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, r14
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov r12, QWORD PTR [rdi+864]
	mov r13, QWORD PTR [rdi+872]
	mov r14, QWORD PTR [rdi+880]
	sub r8, QWORD PTR [rdi+704]
	sbb r9, QWORD PTR [rdi+712]
	sbb r10, QWORD PTR [rdi+720]
	sbb r11, QWORD PTR [rdi+728]
	sbb r12, QWORD PTR [rdi+736]
	sbb r13, QWORD PTR [rdi+744]
	sbb r14, QWORD PTR [rdi+752]
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov r12, QWORD PTR [rdi+864]
	mov r13, QWORD PTR [rdi+872]
	mov r14, QWORD PTR [rdi+880]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+768]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+768]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+776]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+768]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+776]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+784]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+768]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+776]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+784]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+792]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+768]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+776]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+784]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+792]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+800]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+768]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+776]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+784]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+792]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+800]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+808]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+768]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+776]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+784]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+792]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+800]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+808]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+816]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+776]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+784]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+792]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+800]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+808]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+816]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+784]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+792]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+800]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+808]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+816]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+792]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+800]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+808]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+816]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+800]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+808]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+816]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+808]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+816]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+816]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	sub r8, QWORD PTR [rdi+704]
	sbb r9, QWORD PTR [rdi+712]
	sbb r10, QWORD PTR [rdi+720]
	sbb r11, QWORD PTR [rdi+728]
	sbb r12, QWORD PTR [rdi+736]
	sbb r13, QWORD PTR [rdi+744]
	sbb r14, QWORD PTR [rdi+752]
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+896]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+904]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+896]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+904]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+912]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+904]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+912]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+920]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+896]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+904]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+912]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+920]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+928]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+896]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+904]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+912]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+920]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+928]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+936]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+904]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+912]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+920]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+928]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+936]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+944]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+904]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+912]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+920]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+928]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+936]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+944]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+912]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+920]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+928]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+936]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+944]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+920]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+928]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+936]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+944]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+928]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+936]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+944]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+936]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+944]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+944]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, r8
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, r8
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, r8
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, r8
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, r8
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r9
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, r8
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r10
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, r8
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r10
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r11
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, r9
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r11
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, r10
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r11
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r12
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, r11
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r12
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, r12
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r13
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, r13
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, r14
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	mov r12, QWORD PTR [rdi+928]
	mov r13, QWORD PTR [rdi+936]
	mov r14, QWORD PTR [rdi+944]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, r8
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, r8
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, r8
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, r8
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, r8
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r9
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, r8
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r10
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, r8
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r10
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r11
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, r9
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r11
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, r10
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r11
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r12
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, r11
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r12
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, r12
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r13
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, r13
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, r14
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov QWORD PTR [rdi+416], r12
	mov QWORD PTR [rdi+424], r13
	mov QWORD PTR [rdi+432], r14
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	mov r12, QWORD PTR [rdi+928]
	mov r13, QWORD PTR [rdi+936]
	mov r14, QWORD PTR [rdi+944]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+384]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+392]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+384]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+392]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+400]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+392]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+400]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+408]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+384]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+392]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+400]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+408]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+416]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+384]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+392]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+400]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+408]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+416]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+424]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+392]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+400]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+408]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+416]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+424]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+432]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+392]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+400]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+408]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+416]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+424]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+432]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+400]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+408]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+416]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+424]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+432]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+408]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+416]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+424]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+432]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+416]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+424]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+432]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+424]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+432]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+432]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov QWORD PTR [rdi+416], r12
	mov QWORD PTR [rdi+424], r13
	mov QWORD PTR [rdi+432], r14
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+384]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+392]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+384]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+392]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+400]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+392]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+400]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+408]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+384]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+392]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+400]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+408]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+416]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+384]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+392]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+400]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+408]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+416]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+424]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+384]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+392]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+400]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+408]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+416]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+424]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+432]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+392]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+400]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+408]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+416]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+424]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+432]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+400]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+408]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+416]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+424]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+432]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+408]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+416]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+424]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+432]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+416]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+424]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+432]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+424]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+432]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+432]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+448], r8
	mov QWORD PTR [rdi+456], r9
	mov QWORD PTR [rdi+464], r10
	mov QWORD PTR [rdi+472], r11
	mov QWORD PTR [rdi+480], r12
	mov QWORD PTR [rdi+488], r13
	mov QWORD PTR [rdi+496], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+448]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+448]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+456]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+448]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+456]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+464]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+448]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+456]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+464]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+472]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+448]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+456]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+464]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+472]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+480]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+448]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+456]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+464]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+472]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+480]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+488]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+448]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+456]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+464]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+472]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+480]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+488]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+496]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+456]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+464]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+472]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+480]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+488]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+496]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+464]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+472]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+480]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+488]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+496]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+472]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+480]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+488]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+496]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+480]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+488]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+496]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+488]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+496]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+496]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov r12, QWORD PTR [rdi+1664]
	mov r13, QWORD PTR [rdi+1888]
	call {vg_gf448_r64_pow223}
	mov QWORD PTR [rdi+1664], r12
	mov QWORD PTR [rdi+1888], r13
	mov r8, QWORD PTR [rdi+1408]
	mov r9, QWORD PTR [rdi+1416]
	mov r10, QWORD PTR [rdi+1424]
	mov r11, QWORD PTR [rdi+1432]
	mov r12, QWORD PTR [rdi+1440]
	mov r13, QWORD PTR [rdi+1448]
	mov r14, QWORD PTR [rdi+1456]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, r8
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, r8
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, r8
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, r8
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, r8
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r9
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, r8
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r10
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, r8
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r10
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r11
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, r9
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r11
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, r10
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r11
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r12
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, r11
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r12
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, r12
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r13
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, r13
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, r14
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov QWORD PTR [rdi+1456], r14
	mov ebx, 222
23:
	mov r8, QWORD PTR [rdi+1408]
	mov r9, QWORD PTR [rdi+1416]
	mov r10, QWORD PTR [rdi+1424]
	mov r11, QWORD PTR [rdi+1432]
	mov r12, QWORD PTR [rdi+1440]
	mov r13, QWORD PTR [rdi+1448]
	mov r14, QWORD PTR [rdi+1456]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, r8
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, r8
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, r8
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, r8
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, r8
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r9
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, r8
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r10
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, r8
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r10
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r11
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, r9
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r11
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, r10
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r11
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r12
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, r11
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r12
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, r12
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r13
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, r13
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, r14
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov QWORD PTR [rdi+1456], r14
	sub rbx, 1
	jne 23b
	mov r8, QWORD PTR [rdi+1344]
	mov r9, QWORD PTR [rdi+1352]
	mov r10, QWORD PTR [rdi+1360]
	mov r11, QWORD PTR [rdi+1368]
	mov r12, QWORD PTR [rdi+1376]
	mov r13, QWORD PTR [rdi+1384]
	mov r14, QWORD PTR [rdi+1392]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1408]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1416]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1408]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1416]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1424]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1416]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1424]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1432]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1408]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1416]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1424]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1432]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1440]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1408]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1416]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1424]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1432]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1440]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1448]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1416]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1424]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1432]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1440]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1448]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1416]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1424]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1432]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1440]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1448]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1456]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1424]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1432]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1440]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1448]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1456]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1432]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1440]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1448]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1440]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1448]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1456]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1448]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1456]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov QWORD PTR [rdi+1456], r14
	mov r8, QWORD PTR [rdi+1408]
	mov r9, QWORD PTR [rdi+1416]
	mov r10, QWORD PTR [rdi+1424]
	mov r11, QWORD PTR [rdi+1432]
	mov r12, QWORD PTR [rdi+1440]
	mov r13, QWORD PTR [rdi+1448]
	mov r14, QWORD PTR [rdi+1456]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+448]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+448]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+456]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+448]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+456]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+464]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+448]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+456]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+464]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+472]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+448]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+456]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+464]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+472]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+480]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+448]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+456]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+464]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+472]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+480]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+488]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+448]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+456]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+464]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+472]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+480]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+488]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+496]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+456]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+464]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+472]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+480]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+488]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+496]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+464]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+472]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+480]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+488]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+496]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+472]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+480]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+488]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+496]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+480]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+488]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+496]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+488]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+496]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+496]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+448], r8
	mov QWORD PTR [rdi+456], r9
	mov QWORD PTR [rdi+464], r10
	mov QWORD PTR [rdi+472], r11
	mov QWORD PTR [rdi+480], r12
	mov QWORD PTR [rdi+488], r13
	mov QWORD PTR [rdi+496], r14
	mov r8, QWORD PTR [rdi+448]
	mov r9, QWORD PTR [rdi+456]
	mov r10, QWORD PTR [rdi+464]
	mov r11, QWORD PTR [rdi+472]
	mov r12, QWORD PTR [rdi+480]
	mov r13, QWORD PTR [rdi+488]
	mov r14, QWORD PTR [rdi+496]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, r8
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, r8
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, r8
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, r8
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, r8
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r9
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, r8
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r10
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, r8
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r10
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r11
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, r9
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r11
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, r10
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r11
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r12
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, r11
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r12
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, r12
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r13
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, r13
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, r14
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov r12, QWORD PTR [rdi+864]
	mov r13, QWORD PTR [rdi+872]
	mov r14, QWORD PTR [rdi+880]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+256]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+264]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+256]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+264]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+272]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+264]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+272]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+280]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+256]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+264]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+272]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+280]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+288]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+256]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+264]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+272]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+280]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+288]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+296]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+264]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+272]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+280]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+288]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+296]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+304]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+264]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+272]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+280]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+288]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+296]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+304]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+272]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+280]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+288]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+296]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+304]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+280]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+288]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+296]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+304]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+288]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+296]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+304]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+296]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+304]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+304]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov r15d, 1
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov r12, QWORD PTR [rdi+864]
	mov r13, QWORD PTR [rdi+872]
	mov r14, QWORD PTR [rdi+880]
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	sbb r15, r15
	mov rax, QWORD PTR [rdi+832]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+840]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+848]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+856]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+864]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+872]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+880]
	xor r14, rax
	and r14, r15
	xor r14, rax
	mov QWORD PTR [rdi+1712], r8
	mov QWORD PTR [rdi+1720], r9
	mov QWORD PTR [rdi+1728], r10
	mov QWORD PTR [rdi+1736], r11
	mov QWORD PTR [rdi+1744], r12
	mov QWORD PTR [rdi+1752], r13
	mov QWORD PTR [rdi+1760], r14
	mov r15d, 1
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	mov r12, QWORD PTR [rdi+928]
	mov r13, QWORD PTR [rdi+936]
	mov r14, QWORD PTR [rdi+944]
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	sbb r15, r15
	mov rax, QWORD PTR [rdi+896]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+904]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+912]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+920]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+928]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+936]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+944]
	xor r14, rax
	and r14, r15
	xor r14, rax
	mov edx, 0
	mov rax, QWORD PTR [rdi+1712]
	xor rax, r8
	or rdx, rax
	mov rax, QWORD PTR [rdi+1720]
	xor rax, r9
	or rdx, rax
	mov rax, QWORD PTR [rdi+1728]
	xor rax, r10
	or rdx, rax
	mov rax, QWORD PTR [rdi+1736]
	xor rax, r11
	or rdx, rax
	mov rax, QWORD PTR [rdi+1744]
	xor rax, r12
	or rdx, rax
	mov rax, QWORD PTR [rdi+1752]
	xor rax, r13
	or rdx, rax
	mov rax, QWORD PTR [rdi+1760]
	xor rax, r14
	or rdx, rax
	mov rax, QWORD PTR [rdi+1688]
	or rax, rdx
	mov QWORD PTR [rdi+1688], rax
	mov r15d, 1
	mov r8, QWORD PTR [rdi+448]
	mov r9, QWORD PTR [rdi+456]
	mov r10, QWORD PTR [rdi+464]
	mov r11, QWORD PTR [rdi+472]
	mov r12, QWORD PTR [rdi+480]
	mov r13, QWORD PTR [rdi+488]
	mov r14, QWORD PTR [rdi+496]
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	sbb r15, r15
	mov rax, QWORD PTR [rdi+448]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+456]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+464]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+472]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+480]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+488]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+496]
	xor r14, rax
	and r14, r15
	xor r14, rax
	mov rcx, r8
	and rcx, 1
	mov rax, QWORD PTR [rdi+1696]
	xor rcx, rax
	mov edx, 0
	sub rdx, rcx
	mov QWORD PTR [rdi+1704], rdx
	mov rdx, r8
	or rdx, r9
	or rdx, r10
	or rdx, r11
	or rdx, r12
	or rdx, r13
	or rdx, r14
	cmp rdx, 1
	mov edx, 0
	adc rdx, 0
	and rdx, rax
	mov rax, QWORD PTR [rdi+1688]
	or rax, rdx
	mov QWORD PTR [rdi+1688], rax
	mov r8, QWORD PTR [rdi+448]
	mov r9, QWORD PTR [rdi+456]
	mov r10, QWORD PTR [rdi+464]
	mov r11, QWORD PTR [rdi+472]
	mov r12, QWORD PTR [rdi+480]
	mov r13, QWORD PTR [rdi+488]
	mov r14, QWORD PTR [rdi+496]
	sub r8, QWORD PTR [rdi+448]
	sbb r9, QWORD PTR [rdi+456]
	sbb r10, QWORD PTR [rdi+464]
	sbb r11, QWORD PTR [rdi+472]
	sbb r12, QWORD PTR [rdi+480]
	sbb r13, QWORD PTR [rdi+488]
	sbb r14, QWORD PTR [rdi+496]
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov r12, QWORD PTR [rdi+864]
	mov r13, QWORD PTR [rdi+872]
	mov r14, QWORD PTR [rdi+880]
	sub r8, QWORD PTR [rdi+448]
	sbb r9, QWORD PTR [rdi+456]
	sbb r10, QWORD PTR [rdi+464]
	sbb r11, QWORD PTR [rdi+472]
	sbb r12, QWORD PTR [rdi+480]
	sbb r13, QWORD PTR [rdi+488]
	sbb r14, QWORD PTR [rdi+496]
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+448]
	mov rdx, QWORD PTR [rdi+832]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+832], rdx
	mov rax, QWORD PTR [rdi+456]
	mov rdx, QWORD PTR [rdi+840]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+840], rdx
	mov rax, QWORD PTR [rdi+464]
	mov rdx, QWORD PTR [rdi+848]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+848], rdx
	mov rax, QWORD PTR [rdi+472]
	mov rdx, QWORD PTR [rdi+856]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+856], rdx
	mov rax, QWORD PTR [rdi+480]
	mov rdx, QWORD PTR [rdi+864]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+864], rdx
	mov rax, QWORD PTR [rdi+488]
	mov rdx, QWORD PTR [rdi+872]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+872], rdx
	mov rax, QWORD PTR [rdi+496]
	mov rdx, QWORD PTR [rdi+880]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+880], rdx
	mov rsi, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+1880], rsi
	mov rbx, QWORD PTR [rdi+1888]
	sub rbx, 1
	mov QWORD PTR [rdi+1888], rbx
	jne 22b
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	movabs r8, 2749069528532828254
	movabs r9, 4844607530355168142
	movabs r10, 1346042987506197777
	movabs r11, -1554336549866068892
	movabs r12, -7055903183279810713
	movabs r13, 2458144774905870042
	movabs r14, 5699710800930606573
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r14
	movabs r8, -7491604544318539244
	movabs r9, -162952930493216595
	movabs r10, 4239012173876836804
	movabs r11, -8685020228626627881
	movabs r12, 5470311636975982656
	movabs r13, -8613661815248140446
	movabs r14, 7583857750517922852
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov QWORD PTR [rdi+672], r12
	mov QWORD PTR [rdi+680], r13
	mov QWORD PTR [rdi+688], r14
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	mov QWORD PTR [rdi+736], r12
	mov QWORD PTR [rdi+744], r13
	mov QWORD PTR [rdi+752], r14
	movabs r8, -39082
	movabs r9, -1
	movabs r10, -1
	movabs r11, -4294967297
	movabs r12, -1
	movabs r13, -1
	movabs r14, -1
	mov QWORD PTR [rdi+768], r8
	mov QWORD PTR [rdi+776], r9
	mov QWORD PTR [rdi+784], r10
	mov QWORD PTR [rdi+792], r11
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	sub r8, QWORD PTR [rdi+448]
	sbb r9, QWORD PTR [rdi+456]
	sbb r10, QWORD PTR [rdi+464]
	sbb r11, QWORD PTR [rdi+472]
	sbb r12, QWORD PTR [rdi+480]
	sbb r13, QWORD PTR [rdi+488]
	sbb r14, QWORD PTR [rdi+496]
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov QWORD PTR [rdi+448], r8
	mov QWORD PTR [rdi+456], r9
	mov QWORD PTR [rdi+464], r10
	mov QWORD PTR [rdi+472], r11
	mov QWORD PTR [rdi+480], r12
	mov QWORD PTR [rdi+488], r13
	mov QWORD PTR [rdi+496], r14
	mov r8, QWORD PTR [rdi+448]
	mov r9, QWORD PTR [rdi+456]
	mov r10, QWORD PTR [rdi+464]
	mov r11, QWORD PTR [rdi+472]
	mov r12, QWORD PTR [rdi+480]
	mov r13, QWORD PTR [rdi+488]
	mov r14, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r14
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	mov r12, QWORD PTR [rdi+544]
	mov r13, QWORD PTR [rdi+552]
	mov r14, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov QWORD PTR [rdi+672], r12
	mov QWORD PTR [rdi+680], r13
	mov QWORD PTR [rdi+688], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4096], r8
	mov QWORD PTR [rdi+4104], r9
	mov QWORD PTR [rdi+4112], r10
	mov QWORD PTR [rdi+4120], r11
	mov QWORD PTR [rdi+4128], r12
	mov QWORD PTR [rdi+4136], r13
	mov QWORD PTR [rdi+4144], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+4160], r8
	mov QWORD PTR [rdi+4168], r9
	mov QWORD PTR [rdi+4176], r10
	mov QWORD PTR [rdi+4184], r11
	mov QWORD PTR [rdi+4192], r12
	mov QWORD PTR [rdi+4200], r13
	mov QWORD PTR [rdi+4208], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+4224], r8
	mov QWORD PTR [rdi+4232], r9
	mov QWORD PTR [rdi+4240], r10
	mov QWORD PTR [rdi+4248], r11
	mov QWORD PTR [rdi+4256], r12
	mov QWORD PTR [rdi+4264], r13
	mov QWORD PTR [rdi+4272], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4288], r8
	mov QWORD PTR [rdi+4296], r9
	mov QWORD PTR [rdi+4304], r10
	mov QWORD PTR [rdi+4312], r11
	mov QWORD PTR [rdi+4320], r12
	mov QWORD PTR [rdi+4328], r13
	mov QWORD PTR [rdi+4336], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+4352], r8
	mov QWORD PTR [rdi+4360], r9
	mov QWORD PTR [rdi+4368], r10
	mov QWORD PTR [rdi+4376], r11
	mov QWORD PTR [rdi+4384], r12
	mov QWORD PTR [rdi+4392], r13
	mov QWORD PTR [rdi+4400], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+4416], r8
	mov QWORD PTR [rdi+4424], r9
	mov QWORD PTR [rdi+4432], r10
	mov QWORD PTR [rdi+4440], r11
	mov QWORD PTR [rdi+4448], r12
	mov QWORD PTR [rdi+4456], r13
	mov QWORD PTR [rdi+4464], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4480], r8
	mov QWORD PTR [rdi+4488], r9
	mov QWORD PTR [rdi+4496], r10
	mov QWORD PTR [rdi+4504], r11
	mov QWORD PTR [rdi+4512], r12
	mov QWORD PTR [rdi+4520], r13
	mov QWORD PTR [rdi+4528], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+4544], r8
	mov QWORD PTR [rdi+4552], r9
	mov QWORD PTR [rdi+4560], r10
	mov QWORD PTR [rdi+4568], r11
	mov QWORD PTR [rdi+4576], r12
	mov QWORD PTR [rdi+4584], r13
	mov QWORD PTR [rdi+4592], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+4608], r8
	mov QWORD PTR [rdi+4616], r9
	mov QWORD PTR [rdi+4624], r10
	mov QWORD PTR [rdi+4632], r11
	mov QWORD PTR [rdi+4640], r12
	mov QWORD PTR [rdi+4648], r13
	mov QWORD PTR [rdi+4656], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4672], r8
	mov QWORD PTR [rdi+4680], r9
	mov QWORD PTR [rdi+4688], r10
	mov QWORD PTR [rdi+4696], r11
	mov QWORD PTR [rdi+4704], r12
	mov QWORD PTR [rdi+4712], r13
	mov QWORD PTR [rdi+4720], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+4736], r8
	mov QWORD PTR [rdi+4744], r9
	mov QWORD PTR [rdi+4752], r10
	mov QWORD PTR [rdi+4760], r11
	mov QWORD PTR [rdi+4768], r12
	mov QWORD PTR [rdi+4776], r13
	mov QWORD PTR [rdi+4784], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+4800], r8
	mov QWORD PTR [rdi+4808], r9
	mov QWORD PTR [rdi+4816], r10
	mov QWORD PTR [rdi+4824], r11
	mov QWORD PTR [rdi+4832], r12
	mov QWORD PTR [rdi+4840], r13
	mov QWORD PTR [rdi+4848], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4864], r8
	mov QWORD PTR [rdi+4872], r9
	mov QWORD PTR [rdi+4880], r10
	mov QWORD PTR [rdi+4888], r11
	mov QWORD PTR [rdi+4896], r12
	mov QWORD PTR [rdi+4904], r13
	mov QWORD PTR [rdi+4912], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+4928], r8
	mov QWORD PTR [rdi+4936], r9
	mov QWORD PTR [rdi+4944], r10
	mov QWORD PTR [rdi+4952], r11
	mov QWORD PTR [rdi+4960], r12
	mov QWORD PTR [rdi+4968], r13
	mov QWORD PTR [rdi+4976], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+4992], r8
	mov QWORD PTR [rdi+5000], r9
	mov QWORD PTR [rdi+5008], r10
	mov QWORD PTR [rdi+5016], r11
	mov QWORD PTR [rdi+5024], r12
	mov QWORD PTR [rdi+5032], r13
	mov QWORD PTR [rdi+5040], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+5056], r8
	mov QWORD PTR [rdi+5064], r9
	mov QWORD PTR [rdi+5072], r10
	mov QWORD PTR [rdi+5080], r11
	mov QWORD PTR [rdi+5088], r12
	mov QWORD PTR [rdi+5096], r13
	mov QWORD PTR [rdi+5104], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+5120], r8
	mov QWORD PTR [rdi+5128], r9
	mov QWORD PTR [rdi+5136], r10
	mov QWORD PTR [rdi+5144], r11
	mov QWORD PTR [rdi+5152], r12
	mov QWORD PTR [rdi+5160], r13
	mov QWORD PTR [rdi+5168], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5184], r8
	mov QWORD PTR [rdi+5192], r9
	mov QWORD PTR [rdi+5200], r10
	mov QWORD PTR [rdi+5208], r11
	mov QWORD PTR [rdi+5216], r12
	mov QWORD PTR [rdi+5224], r13
	mov QWORD PTR [rdi+5232], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+5248], r8
	mov QWORD PTR [rdi+5256], r9
	mov QWORD PTR [rdi+5264], r10
	mov QWORD PTR [rdi+5272], r11
	mov QWORD PTR [rdi+5280], r12
	mov QWORD PTR [rdi+5288], r13
	mov QWORD PTR [rdi+5296], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov QWORD PTR [rdi+5344], r12
	mov QWORD PTR [rdi+5352], r13
	mov QWORD PTR [rdi+5360], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5376], r8
	mov QWORD PTR [rdi+5384], r9
	mov QWORD PTR [rdi+5392], r10
	mov QWORD PTR [rdi+5400], r11
	mov QWORD PTR [rdi+5408], r12
	mov QWORD PTR [rdi+5416], r13
	mov QWORD PTR [rdi+5424], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+5440], r8
	mov QWORD PTR [rdi+5448], r9
	mov QWORD PTR [rdi+5456], r10
	mov QWORD PTR [rdi+5464], r11
	mov QWORD PTR [rdi+5472], r12
	mov QWORD PTR [rdi+5480], r13
	mov QWORD PTR [rdi+5488], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+5504], r8
	mov QWORD PTR [rdi+5512], r9
	mov QWORD PTR [rdi+5520], r10
	mov QWORD PTR [rdi+5528], r11
	mov QWORD PTR [rdi+5536], r12
	mov QWORD PTR [rdi+5544], r13
	mov QWORD PTR [rdi+5552], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5568], r8
	mov QWORD PTR [rdi+5576], r9
	mov QWORD PTR [rdi+5584], r10
	mov QWORD PTR [rdi+5592], r11
	mov QWORD PTR [rdi+5600], r12
	mov QWORD PTR [rdi+5608], r13
	mov QWORD PTR [rdi+5616], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+5632], r8
	mov QWORD PTR [rdi+5640], r9
	mov QWORD PTR [rdi+5648], r10
	mov QWORD PTR [rdi+5656], r11
	mov QWORD PTR [rdi+5664], r12
	mov QWORD PTR [rdi+5672], r13
	mov QWORD PTR [rdi+5680], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+5696], r8
	mov QWORD PTR [rdi+5704], r9
	mov QWORD PTR [rdi+5712], r10
	mov QWORD PTR [rdi+5720], r11
	mov QWORD PTR [rdi+5728], r12
	mov QWORD PTR [rdi+5736], r13
	mov QWORD PTR [rdi+5744], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5760], r8
	mov QWORD PTR [rdi+5768], r9
	mov QWORD PTR [rdi+5776], r10
	mov QWORD PTR [rdi+5784], r11
	mov QWORD PTR [rdi+5792], r12
	mov QWORD PTR [rdi+5800], r13
	mov QWORD PTR [rdi+5808], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+5824], r8
	mov QWORD PTR [rdi+5832], r9
	mov QWORD PTR [rdi+5840], r10
	mov QWORD PTR [rdi+5848], r11
	mov QWORD PTR [rdi+5856], r12
	mov QWORD PTR [rdi+5864], r13
	mov QWORD PTR [rdi+5872], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+5888], r8
	mov QWORD PTR [rdi+5896], r9
	mov QWORD PTR [rdi+5904], r10
	mov QWORD PTR [rdi+5912], r11
	mov QWORD PTR [rdi+5920], r12
	mov QWORD PTR [rdi+5928], r13
	mov QWORD PTR [rdi+5936], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5952], r8
	mov QWORD PTR [rdi+5960], r9
	mov QWORD PTR [rdi+5968], r10
	mov QWORD PTR [rdi+5976], r11
	mov QWORD PTR [rdi+5984], r12
	mov QWORD PTR [rdi+5992], r13
	mov QWORD PTR [rdi+6000], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+6016], r8
	mov QWORD PTR [rdi+6024], r9
	mov QWORD PTR [rdi+6032], r10
	mov QWORD PTR [rdi+6040], r11
	mov QWORD PTR [rdi+6048], r12
	mov QWORD PTR [rdi+6056], r13
	mov QWORD PTR [rdi+6064], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+6080], r8
	mov QWORD PTR [rdi+6088], r9
	mov QWORD PTR [rdi+6096], r10
	mov QWORD PTR [rdi+6104], r11
	mov QWORD PTR [rdi+6112], r12
	mov QWORD PTR [rdi+6120], r13
	mov QWORD PTR [rdi+6128], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+6144], r8
	mov QWORD PTR [rdi+6152], r9
	mov QWORD PTR [rdi+6160], r10
	mov QWORD PTR [rdi+6168], r11
	mov QWORD PTR [rdi+6176], r12
	mov QWORD PTR [rdi+6184], r13
	mov QWORD PTR [rdi+6192], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+6208], r8
	mov QWORD PTR [rdi+6216], r9
	mov QWORD PTR [rdi+6224], r10
	mov QWORD PTR [rdi+6232], r11
	mov QWORD PTR [rdi+6240], r12
	mov QWORD PTR [rdi+6248], r13
	mov QWORD PTR [rdi+6256], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+6272], r8
	mov QWORD PTR [rdi+6280], r9
	mov QWORD PTR [rdi+6288], r10
	mov QWORD PTR [rdi+6296], r11
	mov QWORD PTR [rdi+6304], r12
	mov QWORD PTR [rdi+6312], r13
	mov QWORD PTR [rdi+6320], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+6336], r8
	mov QWORD PTR [rdi+6344], r9
	mov QWORD PTR [rdi+6352], r10
	mov QWORD PTR [rdi+6360], r11
	mov QWORD PTR [rdi+6368], r12
	mov QWORD PTR [rdi+6376], r13
	mov QWORD PTR [rdi+6384], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+6400], r8
	mov QWORD PTR [rdi+6408], r9
	mov QWORD PTR [rdi+6416], r10
	mov QWORD PTR [rdi+6424], r11
	mov QWORD PTR [rdi+6432], r12
	mov QWORD PTR [rdi+6440], r13
	mov QWORD PTR [rdi+6448], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+6464], r8
	mov QWORD PTR [rdi+6472], r9
	mov QWORD PTR [rdi+6480], r10
	mov QWORD PTR [rdi+6488], r11
	mov QWORD PTR [rdi+6496], r12
	mov QWORD PTR [rdi+6504], r13
	mov QWORD PTR [rdi+6512], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+6528], r8
	mov QWORD PTR [rdi+6536], r9
	mov QWORD PTR [rdi+6544], r10
	mov QWORD PTR [rdi+6552], r11
	mov QWORD PTR [rdi+6560], r12
	mov QWORD PTR [rdi+6568], r13
	mov QWORD PTR [rdi+6576], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+6592], r8
	mov QWORD PTR [rdi+6600], r9
	mov QWORD PTR [rdi+6608], r10
	mov QWORD PTR [rdi+6616], r11
	mov QWORD PTR [rdi+6624], r12
	mov QWORD PTR [rdi+6632], r13
	mov QWORD PTR [rdi+6640], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+6656], r8
	mov QWORD PTR [rdi+6664], r9
	mov QWORD PTR [rdi+6672], r10
	mov QWORD PTR [rdi+6680], r11
	mov QWORD PTR [rdi+6688], r12
	mov QWORD PTR [rdi+6696], r13
	mov QWORD PTR [rdi+6704], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+6720], r8
	mov QWORD PTR [rdi+6728], r9
	mov QWORD PTR [rdi+6736], r10
	mov QWORD PTR [rdi+6744], r11
	mov QWORD PTR [rdi+6752], r12
	mov QWORD PTR [rdi+6760], r13
	mov QWORD PTR [rdi+6768], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+6784], r8
	mov QWORD PTR [rdi+6792], r9
	mov QWORD PTR [rdi+6800], r10
	mov QWORD PTR [rdi+6808], r11
	mov QWORD PTR [rdi+6816], r12
	mov QWORD PTR [rdi+6824], r13
	mov QWORD PTR [rdi+6832], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+6848], r8
	mov QWORD PTR [rdi+6856], r9
	mov QWORD PTR [rdi+6864], r10
	mov QWORD PTR [rdi+6872], r11
	mov QWORD PTR [rdi+6880], r12
	mov QWORD PTR [rdi+6888], r13
	mov QWORD PTR [rdi+6896], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+6912], r8
	mov QWORD PTR [rdi+6920], r9
	mov QWORD PTR [rdi+6928], r10
	mov QWORD PTR [rdi+6936], r11
	mov QWORD PTR [rdi+6944], r12
	mov QWORD PTR [rdi+6952], r13
	mov QWORD PTR [rdi+6960], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+6976], r8
	mov QWORD PTR [rdi+6984], r9
	mov QWORD PTR [rdi+6992], r10
	mov QWORD PTR [rdi+7000], r11
	mov QWORD PTR [rdi+7008], r12
	mov QWORD PTR [rdi+7016], r13
	mov QWORD PTR [rdi+7024], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+7040], r8
	mov QWORD PTR [rdi+7048], r9
	mov QWORD PTR [rdi+7056], r10
	mov QWORD PTR [rdi+7064], r11
	mov QWORD PTR [rdi+7072], r12
	mov QWORD PTR [rdi+7080], r13
	mov QWORD PTR [rdi+7088], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+7104], r8
	mov QWORD PTR [rdi+7112], r9
	mov QWORD PTR [rdi+7120], r10
	mov QWORD PTR [rdi+7128], r11
	mov QWORD PTR [rdi+7136], r12
	mov QWORD PTR [rdi+7144], r13
	mov QWORD PTR [rdi+7152], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+7168], r8
	mov QWORD PTR [rdi+7176], r9
	mov QWORD PTR [rdi+7184], r10
	mov QWORD PTR [rdi+7192], r11
	mov QWORD PTR [rdi+7200], r12
	mov QWORD PTR [rdi+7208], r13
	mov QWORD PTR [rdi+7216], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+7232], r8
	mov QWORD PTR [rdi+7240], r9
	mov QWORD PTR [rdi+7248], r10
	mov QWORD PTR [rdi+7256], r11
	mov QWORD PTR [rdi+7264], r12
	mov QWORD PTR [rdi+7272], r13
	mov QWORD PTR [rdi+7280], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+7296], r8
	mov QWORD PTR [rdi+7304], r9
	mov QWORD PTR [rdi+7312], r10
	mov QWORD PTR [rdi+7320], r11
	mov QWORD PTR [rdi+7328], r12
	mov QWORD PTR [rdi+7336], r13
	mov QWORD PTR [rdi+7344], r14
	mov ebx, 0
	mov ecx, 16
24:
	movzx eax, BYTE PTR [rdi+rbx*1+2052]
	movzx edx, BYTE PTR [rdi+rbx*1+2051]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2050]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2049]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	add rax, rcx
	add rax, 16
	and rax, 31
	mov r15, rax
	sub r15, 32
	cmp rax, 16
	cmovb r15, rax
	test rax, 1
	mov eax, 0
	cmove r15, rax
	add rcx, rdx
	add rcx, 16
	sub rcx, r15
	shr rcx, 1
	mov BYTE PTR [rdi+rbx*1+3072], r15b
	add rbx, 1
	cmp rbx, 456
	jne 24b
	mov eax, 0
	mov edx, 0
	add rax, rcx
	add rax, 16
	and rax, 31
	mov r15, rax
	sub r15, 32
	cmp rax, 16
	cmovb r15, rax
	test rax, 1
	mov eax, 0
	cmove r15, rax
	add rcx, rdx
	add rcx, 16
	sub rcx, r15
	shr rcx, 1
	mov BYTE PTR [rdi+rbx*1+3072], r15b
	add rbx, 1
	mov eax, 0
	mov edx, 0
	add rax, rcx
	add rax, 16
	and rax, 31
	mov r15, rax
	sub r15, 32
	cmp rax, 16
	cmovb r15, rax
	test rax, 1
	mov eax, 0
	cmove r15, rax
	add rcx, rdx
	add rcx, 16
	sub rcx, r15
	shr rcx, 1
	mov BYTE PTR [rdi+rbx*1+3072], r15b
	add rbx, 1
	mov eax, 0
	mov edx, 0
	add rax, rcx
	add rax, 16
	and rax, 31
	mov r15, rax
	sub r15, 32
	cmp rax, 16
	cmovb r15, rax
	test rax, 1
	mov eax, 0
	cmove r15, rax
	add rcx, rdx
	add rcx, 16
	sub rcx, r15
	shr rcx, 1
	mov BYTE PTR [rdi+rbx*1+3072], r15b
	add rbx, 1
	mov eax, 0
	mov edx, 0
	add rax, rcx
	add rax, 16
	and rax, 31
	mov r15, rax
	sub r15, 32
	cmp rax, 16
	cmovb r15, rax
	test rax, 1
	mov eax, 0
	cmove r15, rax
	add rcx, rdx
	add rcx, 16
	sub rcx, r15
	shr rcx, 1
	mov BYTE PTR [rdi+rbx*1+3072], r15b
	add rbx, 1
	mov eax, 0
	mov edx, 0
	add rax, rcx
	add rax, 16
	and rax, 31
	mov r15, rax
	sub r15, 32
	cmp rax, 16
	cmovb r15, rax
	test rax, 1
	mov eax, 0
	cmove r15, rax
	add rcx, rdx
	add rcx, 16
	sub rcx, r15
	shr rcx, 1
	mov BYTE PTR [rdi+rbx*1+3072], r15b
	add rbx, 1
	mov ebx, 0
	mov ecx, 16
25:
	movzx eax, BYTE PTR [rdi+rbx*1+2564]
	movzx edx, BYTE PTR [rdi+rbx*1+2563]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2562]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2561]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2560]
	add rax, rax
	add rax, rdx
	add rax, rcx
	add rax, 16
	and rax, 31
	mov r15, rax
	sub r15, 32
	cmp rax, 16
	cmovb r15, rax
	test rax, 1
	mov eax, 0
	cmove r15, rax
	add rcx, rdx
	add rcx, 16
	sub rcx, r15
	shr rcx, 1
	mov BYTE PTR [rdi+rbx*1+3536], r15b
	add rbx, 1
	cmp rbx, 456
	jne 25b
	mov eax, 0
	mov edx, 0
	add rax, rcx
	add rax, 16
	and rax, 31
	mov r15, rax
	sub r15, 32
	cmp rax, 16
	cmovb r15, rax
	test rax, 1
	mov eax, 0
	cmove r15, rax
	add rcx, rdx
	add rcx, 16
	sub rcx, r15
	shr rcx, 1
	mov BYTE PTR [rdi+rbx*1+3536], r15b
	add rbx, 1
	mov eax, 0
	mov edx, 0
	add rax, rcx
	add rax, 16
	and rax, 31
	mov r15, rax
	sub r15, 32
	cmp rax, 16
	cmovb r15, rax
	test rax, 1
	mov eax, 0
	cmove r15, rax
	add rcx, rdx
	add rcx, 16
	sub rcx, r15
	shr rcx, 1
	mov BYTE PTR [rdi+rbx*1+3536], r15b
	add rbx, 1
	mov eax, 0
	mov edx, 0
	add rax, rcx
	add rax, 16
	and rax, 31
	mov r15, rax
	sub r15, 32
	cmp rax, 16
	cmovb r15, rax
	test rax, 1
	mov eax, 0
	cmove r15, rax
	add rcx, rdx
	add rcx, 16
	sub rcx, r15
	shr rcx, 1
	mov BYTE PTR [rdi+rbx*1+3536], r15b
	add rbx, 1
	mov eax, 0
	mov edx, 0
	add rax, rcx
	add rax, 16
	and rax, 31
	mov r15, rax
	sub r15, 32
	cmp rax, 16
	cmovb r15, rax
	test rax, 1
	mov eax, 0
	cmove r15, rax
	add rcx, rdx
	add rcx, 16
	sub rcx, r15
	shr rcx, 1
	mov BYTE PTR [rdi+rbx*1+3536], r15b
	add rbx, 1
	mov eax, 0
	mov edx, 0
	add rax, rcx
	add rax, 16
	and rax, 31
	mov r15, rax
	sub r15, 32
	cmp rax, 16
	cmovb r15, rax
	test rax, 1
	mov eax, 0
	cmove r15, rax
	add rcx, rdx
	add rcx, 16
	sub rcx, r15
	shr rcx, 1
	mov BYTE PTR [rdi+rbx*1+3536], r15b
	add rbx, 1
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov ebx, 461
26:
	sub rbx, 1
	call {vg_ed448_r64_point_double}
	movzx r15d, BYTE PTR [rdi+rbx*1+3072]
	test r15, r15
	jne 27f
	jmp 28f
27:
	mov eax, 256
	sub rax, r15
	cmp r15, 128
	cmovae r15, rax
	cmp r15, 0
	movabs rax, 0
	cmove r8, rax
	movabs rax, 0
	cmove r9, rax
	movabs rax, 0
	cmove r10, rax
	movabs rax, 0
	cmove r11, rax
	movabs rax, 0
	cmove r12, rax
	movabs rax, 0
	cmove r13, rax
	movabs rax, 0
	cmove r14, rax
	cmp r15, 1
	movabs rax, 2749069528532828254
	cmove r8, rax
	movabs rax, 4844607530355168142
	cmove r9, rax
	movabs rax, 1346042987506197777
	cmove r10, rax
	movabs rax, -1554336549866068892
	cmove r11, rax
	movabs rax, -7055903183279810713
	cmove r12, rax
	movabs rax, 2458144774905870042
	cmove r13, rax
	movabs rax, 5699710800930606573
	cmove r14, rax
	cmp r15, 2
	movabs rax, 6148914691236517205
	cmove r8, rax
	movabs rax, 6148914691236517205
	cmove r9, rax
	movabs rax, 6148914691236517205
	cmove r10, rax
	movabs rax, -6148914696963140267
	cmove r11, rax
	movabs rax, -6148914691236517206
	cmove r12, rax
	movabs rax, -6148914691236517206
	cmove r13, rax
	movabs rax, -6148914691236517206
	cmove r14, rax
	cmp r15, 3
	movabs rax, 6280295186148831119
	cmove r8, rax
	movabs rax, -1701596046412634025
	cmove r9, rax
	movabs rax, -2690395036530040874
	cmove r10, rax
	movabs rax, -2109365253656555544
	cmove r11, rax
	movabs rax, 3613043087235515079
	cmove r12, rax
	movabs rax, 6178204427262268467
	cmove r13, rax
	movabs rax, 605039720527343460
	cmove r14, rax
	cmp r15, 4
	movabs rax, -2103670668213453008
	cmove r8, rax
	movabs rax, 2427125161309888800
	cmove r9, rax
	movabs rax, 123776358925850810
	cmove r10, rax
	movabs rax, -7782883443183498045
	cmove r11, rax
	movabs rax, 2691474513279357382
	cmove r12, rax
	movabs rax, 1448366266828532202
	cmove r13, rax
	movabs rax, 5322335964780875308
	cmove r14, rax
	cmp r15, 5
	movabs rax, -3411022548261732300
	cmove r8, rax
	movabs rax, -1118249999129970352
	cmove r9, rax
	movabs rax, -8376460584496120682
	cmove r10, rax
	movabs rax, 6257577858823623296
	cmove r11, rax
	movabs rax, -9166004525811454553
	cmove r12, rax
	movabs rax, 3145588550694931951
	cmove r13, rax
	movabs rax, 8835942852527508238
	cmove r14, rax
	cmp r15, 6
	movabs rax, 8682895436102432668
	cmove r8, rax
	movabs rax, 8145160288462980008
	cmove r9, rax
	movabs rax, 8522249051738001706
	cmove r10, rax
	movabs rax, 5393446917391180968
	cmove r11, rax
	movabs rax, -1840851835041354485
	cmove r12, rax
	movabs rax, 14807036545017298
	cmove r13, rax
	movabs rax, 6075987035410887214
	cmove r14, rax
	cmp r15, 7
	movabs rax, -2891428162666370313
	cmove r8, rax
	movabs rax, 7929450305363086023
	cmove r9, rax
	movabs rax, -5358710516878404496
	cmove r10, rax
	movabs rax, -3068949691208448080
	cmove r11, rax
	movabs rax, -947792828850093533
	cmove r12, rax
	movabs rax, 5078822684213041034
	cmove r13, rax
	movabs rax, 546986031499177847
	cmove r14, rax
	cmp r15, 8
	movabs rax, -7627628106365026848
	cmove r8, rax
	movabs rax, 8159997210744063670
	cmove r9, rax
	movabs rax, -9121367074540764755
	cmove r10, rax
	movabs rax, -8801006089315502979
	cmove r11, rax
	movabs rax, 251085449600968790
	cmove r12, rax
	movabs rax, 7204428792430582139
	cmove r13, rax
	movabs rax, -3318664376584985765
	cmove r14, rax
	cmp r15, 9
	movabs rax, 8736154174307919979
	cmove r8, rax
	movabs rax, -8508115230956150916
	cmove r9, rax
	movabs rax, 3504039371814009993
	cmove r10, rax
	movabs rax, 1778153217144534084
	cmove r11, rax
	movabs rax, 7843829989666696819
	cmove r12, rax
	movabs rax, -8297926136368877830
	cmove r13, rax
	movabs rax, -1218697799881392982
	cmove r14, rax
	cmp r15, 10
	movabs rax, 4269466760113893437
	cmove r8, rax
	movabs rax, 4443756583335305943
	cmove r9, rax
	movabs rax, -6478952820923473458
	cmove r10, rax
	movabs rax, 4698613305028278444
	cmove r11, rax
	movabs rax, 1816715556992998403
	cmove r12, rax
	movabs rax, -2506865564300724745
	cmove r13, rax
	movabs rax, 8595242609372709148
	cmove r14, rax
	cmp r15, 11
	movabs rax, -5120788901081005814
	cmove r8, rax
	movabs rax, 2974736480797561869
	cmove r9, rax
	movabs rax, 6349436529673541679
	cmove r10, rax
	movabs rax, 1175246166531061621
	cmove r11, rax
	movabs rax, 987715678637272807
	cmove r12, rax
	movabs rax, -1914749314047910588
	cmove r13, rax
	movabs rax, -4678488238337757519
	cmove r14, rax
	cmp r15, 12
	movabs rax, -8765992267841426236
	cmove r8, rax
	movabs rax, 7876105385696401782
	cmove r9, rax
	movabs rax, 6318841490082490643
	cmove r10, rax
	movabs rax, -6799098456004849302
	cmove r11, rax
	movabs rax, 7950041422219400142
	cmove r12, rax
	movabs rax, -6518371319308379543
	cmove r13, rax
	movabs rax, 2367228065212506915
	cmove r14, rax
	cmp r15, 13
	movabs rax, 360447631085777393
	cmove r8, rax
	movabs rax, -407002234465224250
	cmove r9, rax
	movabs rax, 4923889924515193451
	cmove r10, rax
	movabs rax, 122505256646398243
	cmove r11, rax
	movabs rax, 4971014152642700069
	cmove r12, rax
	movabs rax, -4994841729549504347
	cmove r13, rax
	movabs rax, 841853374045687558
	cmove r14, rax
	cmp r15, 14
	movabs rax, 7177421125526727146
	cmove r8, rax
	movabs rax, 8315865734813239757
	cmove r9, rax
	movabs rax, 4489359356980983987
	cmove r10, rax
	movabs rax, -7044416701442103241
	cmove r11, rax
	movabs rax, -8568714059398251619
	cmove r12, rax
	movabs rax, 4896544764392199533
	cmove r13, rax
	movabs rax, -3974973683566427882
	cmove r14, rax
	cmp r15, 15
	movabs rax, 2833429670568339929
	cmove r8, rax
	movabs rax, 3880791610977972515
	cmove r9, rax
	movabs rax, 2877555668162950192
	cmove r10, rax
	movabs rax, 1586781174018207369
	cmove r11, rax
	movabs rax, -288986243257629230
	cmove r12, rax
	movabs rax, -639049920591346206
	cmove r13, rax
	movabs rax, 3519238486955185078
	cmove r14, rax
	cmp r15, 16
	movabs rax, -8075598463790611870
	cmove r8, rax
	movabs rax, -8314661957360023690
	cmove r9, rax
	movabs rax, -183307860578173226
	cmove r10, rax
	movabs rax, 8024079311250104042
	cmove r11, rax
	movabs rax, -1681786569951160867
	cmove r12, rax
	movabs rax, 7967589090445963309
	cmove r13, rax
	movabs rax, -2484857849886367850
	cmove r14, rax
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r14
	cmp r15, 0
	movabs rax, 1
	cmove r8, rax
	movabs rax, 0
	cmove r9, rax
	movabs rax, 0
	cmove r10, rax
	movabs rax, 0
	cmove r11, rax
	movabs rax, 0
	cmove r12, rax
	movabs rax, 0
	cmove r13, rax
	movabs rax, 0
	cmove r14, rax
	cmp r15, 1
	movabs rax, -7491604544318539244
	cmove r8, rax
	movabs rax, -162952930493216595
	cmove r9, rax
	movabs rax, 4239012173876836804
	cmove r10, rax
	movabs rax, -8685020228626627881
	cmove r11, rax
	movabs rax, 5470311636975982656
	cmove r12, rax
	movabs rax, -8613661815248140446
	cmove r13, rax
	movabs rax, 7583857750517922852
	cmove r14, rax
	cmp r15, 2
	movabs rax, -2672046567068563731
	cmove r8, rax
	movabs rax, -4918860160361979797
	cmove r9, rax
	movabs rax, 965289309431804056
	cmove r10, rax
	movabs rax, -5196189206332259144
	cmove r11, rax
	movabs rax, 247372112644820439
	cmove r12, rax
	movabs rax, -5523148033714896208
	cmove r13, rax
	movabs rax, -5907058723559897971
	cmove r14, rax
	cmp r15, 3
	movabs rax, -5178387422432536836
	cmove r8, rax
	movabs rax, -4613205092545319505
	cmove r9, rax
	movabs rax, -4955592245229688848
	cmove r10, rax
	movabs rax, -223987548453724840
	cmove r11, rax
	movabs rax, -7328889771909528647
	cmove r12, rax
	movabs rax, 489725205581309508
	cmove r13, rax
	movabs rax, -2304249972204086025
	cmove r14, rax
	cmp r15, 4
	movabs rax, 3666553487256524857
	cmove r8, rax
	movabs rax, -5344571917631402149
	cmove r9, rax
	movabs rax, -4550613101182282638
	cmove r10, rax
	movabs rax, -3959293944519828543
	cmove r11, rax
	movabs rax, -7154038174885881787
	cmove r12, rax
	movabs rax, 1606434479575014295
	cmove r13, rax
	movabs rax, -3129869916987071193
	cmove r14, rax
	cmp r15, 5
	movabs rax, 4878650828014237163
	cmove r8, rax
	movabs rax, 6359176211928654420
	cmove r9, rax
	movabs rax, 2870944631088132924
	cmove r10, rax
	movabs rax, -2853784664507154063
	cmove r11, rax
	movabs rax, 2741743853864325070
	cmove r12, rax
	movabs rax, -5111413069748630818
	cmove r13, rax
	movabs rax, -5909438380888298029
	cmove r14, rax
	cmp r15, 6
	movabs rax, -8292713382021399604
	cmove r8, rax
	movabs rax, 3116153286685855401
	cmove r9, rax
	movabs rax, -2161979058868550115
	cmove r10, rax
	movabs rax, 7621644326692353718
	cmove r11, rax
	movabs rax, 6026509380738552344
	cmove r12, rax
	movabs rax, 8376343835884109776
	cmove r13, rax
	movabs rax, 4582898388272815149
	cmove r14, rax
	cmp r15, 7
	movabs rax, 712146258225805183
	cmove r8, rax
	movabs rax, -4920405895120737444
	cmove r9, rax
	movabs rax, 3424083548011379776
	cmove r10, rax
	movabs rax, -3857063638297131267
	cmove r11, rax
	movabs rax, -7763785256769941952
	cmove r12, rax
	movabs rax, 8319200410271463541
	cmove r13, rax
	movabs rax, 9069926653236177308
	cmove r14, rax
	cmp r15, 8
	movabs rax, 4994131844324253851
	cmove r8, rax
	movabs rax, -2837524625388484370
	cmove r9, rax
	movabs rax, -8742188326640927832
	cmove r10, rax
	movabs rax, 8924248229044349651
	cmove r11, rax
	movabs rax, 4651210406443137339
	cmove r12, rax
	movabs rax, -1694163570364823878
	cmove r13, rax
	movabs rax, -4082988813122888742
	cmove r14, rax
	cmp r15, 9
	movabs rax, -8383646460407417521
	cmove r8, rax
	movabs rax, 1243263070416860155
	cmove r9, rax
	movabs rax, 2697580618709811863
	cmove r10, rax
	movabs rax, -5016914940601297446
	cmove r11, rax
	movabs rax, -8329273835438119430
	cmove r12, rax
	movabs rax, -5802101051401309615
	cmove r13, rax
	movabs rax, 1540431362170990125
	cmove r14, rax
	cmp r15, 10
	movabs rax, -5650528201356746905
	cmove r8, rax
	movabs rax, 900266382339179958
	cmove r9, rax
	movabs rax, -487486519639364644
	cmove r10, rax
	movabs rax, -581481971037807349
	cmove r11, rax
	movabs rax, -1680943031179928293
	cmove r12, rax
	movabs rax, 2662173830588720664
	cmove r13, rax
	movabs rax, 5561921397832016144
	cmove r14, rax
	cmp r15, 11
	movabs rax, -6121295724902174975
	cmove r8, rax
	movabs rax, -138898871194534516
	cmove r9, rax
	movabs rax, -3456947545662473682
	cmove r10, rax
	movabs rax, 491323330243982853
	cmove r11, rax
	movabs rax, 71789713185410904
	cmove r12, rax
	movabs rax, 3495114231185090761
	cmove r13, rax
	movabs rax, 4815292848493755821
	cmove r14, rax
	cmp r15, 12
	movabs rax, -3351166182381838681
	cmove r8, rax
	movabs rax, -5462944085567607886
	cmove r9, rax
	movabs rax, -5972438006519978297
	cmove r10, rax
	movabs rax, 2568174706127723596
	cmove r11, rax
	movabs rax, 7233661737621619868
	cmove r12, rax
	movabs rax, -39612835361303833
	cmove r13, rax
	movabs rax, 5607328683565661187
	cmove r14, rax
	cmp r15, 13
	movabs rax, -1633859514724484635
	cmove r8, rax
	movabs rax, -7214180089503789373
	cmove r9, rax
	movabs rax, -6929009915902812709
	cmove r10, rax
	movabs rax, -9015294007109290219
	cmove r11, rax
	movabs rax, 4761684212221991079
	cmove r12, rax
	movabs rax, -3067505480195091360
	cmove r13, rax
	movabs rax, -4207623256675824588
	cmove r14, rax
	cmp r15, 14
	movabs rax, 1087600364922830972
	cmove r8, rax
	movabs rax, -4650418231718444217
	cmove r9, rax
	movabs rax, 9075344222383677674
	cmove r10, rax
	movabs rax, 2196474243079848590
	cmove r11, rax
	movabs rax, -2520852319105388836
	cmove r12, rax
	movabs rax, -4005962050623016591
	cmove r13, rax
	movabs rax, 7395609526103497572
	cmove r14, rax
	cmp r15, 15
	movabs rax, 5634115148821066947
	cmove r8, rax
	movabs rax, -480202629429682072
	cmove r9, rax
	movabs rax, -983754472051857565
	cmove r10, rax
	movabs rax, -6960780143603279415
	cmove r11, rax
	movabs rax, 2459863876061731974
	cmove r12, rax
	movabs rax, -8736224005398037755
	cmove r13, rax
	movabs rax, -824236854934107447
	cmove r14, rax
	cmp r15, 16
	movabs rax, 922647402217568645
	cmove r8, rax
	movabs rax, 6408432882851236482
	cmove r9, rax
	movabs rax, 5096959009381795889
	cmove r10, rax
	movabs rax, -7349430997802707930
	cmove r11, rax
	movabs rax, -1107486604588770261
	cmove r12, rax
	movabs rax, 8361698052185718522
	cmove r13, rax
	movabs rax, 1923796597625681521
	cmove r14, rax
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov QWORD PTR [rdi+672], r12
	mov QWORD PTR [rdi+680], r13
	mov QWORD PTR [rdi+688], r14
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	sub r8, QWORD PTR [rdi+576]
	sbb r9, QWORD PTR [rdi+584]
	sbb r10, QWORD PTR [rdi+592]
	sbb r11, QWORD PTR [rdi+600]
	sbb r12, QWORD PTR [rdi+608]
	sbb r13, QWORD PTR [rdi+616]
	sbb r14, QWORD PTR [rdi+624]
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	mov r8, QWORD PTR [rdi+576]
	mov r9, QWORD PTR [rdi+584]
	mov r10, QWORD PTR [rdi+592]
	mov r11, QWORD PTR [rdi+600]
	mov r12, QWORD PTR [rdi+608]
	mov r13, QWORD PTR [rdi+616]
	mov r14, QWORD PTR [rdi+624]
	movzx eax, BYTE PTR [rdi+rbx*1+3072]
	and rax, 128
	cmp rax, 128
	cmove r8, QWORD PTR [rdi+256]
	cmove r9, QWORD PTR [rdi+264]
	cmove r10, QWORD PTR [rdi+272]
	cmove r11, QWORD PTR [rdi+280]
	cmove r12, QWORD PTR [rdi+288]
	cmove r13, QWORD PTR [rdi+296]
	cmove r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
28:
	movzx r15d, BYTE PTR [rdi+rbx*1+3536]
	test r15, r15
	jne 29f
	jmp 210f
29:
	mov eax, 256
	sub rax, r15
	cmp r15, 128
	cmovae r15, rax
	mov rax, r15
	mov edx, 192
	mul rdx
	mov r15, rax
	mov r8, QWORD PTR [rdi+r15*1+4096]
	mov r9, QWORD PTR [rdi+r15*1+4104]
	mov r10, QWORD PTR [rdi+r15*1+4112]
	mov r11, QWORD PTR [rdi+r15*1+4120]
	mov r12, QWORD PTR [rdi+r15*1+4128]
	mov r13, QWORD PTR [rdi+r15*1+4136]
	mov r14, QWORD PTR [rdi+r15*1+4144]
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r14
	mov r8, QWORD PTR [rdi+r15*1+4160]
	mov r9, QWORD PTR [rdi+r15*1+4168]
	mov r10, QWORD PTR [rdi+r15*1+4176]
	mov r11, QWORD PTR [rdi+r15*1+4184]
	mov r12, QWORD PTR [rdi+r15*1+4192]
	mov r13, QWORD PTR [rdi+r15*1+4200]
	mov r14, QWORD PTR [rdi+r15*1+4208]
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov QWORD PTR [rdi+672], r12
	mov QWORD PTR [rdi+680], r13
	mov QWORD PTR [rdi+688], r14
	mov r8, QWORD PTR [rdi+r15*1+4224]
	mov r9, QWORD PTR [rdi+r15*1+4232]
	mov r10, QWORD PTR [rdi+r15*1+4240]
	mov r11, QWORD PTR [rdi+r15*1+4248]
	mov r12, QWORD PTR [rdi+r15*1+4256]
	mov r13, QWORD PTR [rdi+r15*1+4264]
	mov r14, QWORD PTR [rdi+r15*1+4272]
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	mov QWORD PTR [rdi+736], r12
	mov QWORD PTR [rdi+744], r13
	mov QWORD PTR [rdi+752], r14
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	sub r8, QWORD PTR [rdi+576]
	sbb r9, QWORD PTR [rdi+584]
	sbb r10, QWORD PTR [rdi+592]
	sbb r11, QWORD PTR [rdi+600]
	sbb r12, QWORD PTR [rdi+608]
	sbb r13, QWORD PTR [rdi+616]
	sbb r14, QWORD PTR [rdi+624]
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	mov r8, QWORD PTR [rdi+576]
	mov r9, QWORD PTR [rdi+584]
	mov r10, QWORD PTR [rdi+592]
	mov r11, QWORD PTR [rdi+600]
	mov r12, QWORD PTR [rdi+608]
	mov r13, QWORD PTR [rdi+616]
	mov r14, QWORD PTR [rdi+624]
	movzx eax, BYTE PTR [rdi+rbx*1+3536]
	and rax, 128
	cmp rax, 128
	cmove r8, QWORD PTR [rdi+256]
	cmove r9, QWORD PTR [rdi+264]
	cmove r10, QWORD PTR [rdi+272]
	cmove r11, QWORD PTR [rdi+280]
	cmove r12, QWORD PTR [rdi+288]
	cmove r13, QWORD PTR [rdi+296]
	cmove r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r14
	mov r8, QWORD PTR [rdi+704]
	mov r9, QWORD PTR [rdi+712]
	mov r10, QWORD PTR [rdi+720]
	mov r11, QWORD PTR [rdi+728]
	mov r12, QWORD PTR [rdi+736]
	mov r13, QWORD PTR [rdi+744]
	mov r14, QWORD PTR [rdi+752]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+192]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+200]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+192]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+200]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+208]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+200]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+208]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+216]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+192]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+200]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+208]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+216]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+224]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+192]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+200]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+208]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+216]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+224]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+232]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+200]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+208]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+216]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+224]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+232]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+240]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+200]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+208]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+216]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+224]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+232]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+240]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+208]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+216]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+224]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+232]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+240]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+216]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+224]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+232]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+240]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+224]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+232]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+240]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+232]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+240]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+240]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	call {vg_ed448_r64_point_add_affine}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
210:
	test rbx, rbx
	jne 26b
	mov ebx, 2
211:
	call {vg_ed448_r64_point_double}
	sub rbx, 1
	jne 211b
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov QWORD PTR [rdi+416], r12
	mov QWORD PTR [rdi+424], r13
	mov QWORD PTR [rdi+432], r14
	mov r8, QWORD PTR [rdi+1768]
	mov r9, QWORD PTR [rdi+1776]
	mov r10, QWORD PTR [rdi+1784]
	mov r11, QWORD PTR [rdi+1792]
	mov r12, QWORD PTR [rdi+1800]
	mov r13, QWORD PTR [rdi+1808]
	mov r14, QWORD PTR [rdi+1816]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+1824]
	mov r9, QWORD PTR [rdi+1832]
	mov r10, QWORD PTR [rdi+1840]
	mov r11, QWORD PTR [rdi+1848]
	mov r12, QWORD PTR [rdi+1856]
	mov r13, QWORD PTR [rdi+1864]
	mov r14, QWORD PTR [rdi+1872]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	mov ebx, 2
212:
	call {vg_ed448_r64_point_double}
	sub rbx, 1
	jne 212b
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+256]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+264]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+256]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+264]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+272]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+264]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+272]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+280]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+256]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+264]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+272]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+280]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+288]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+256]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+264]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+272]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+280]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+288]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+296]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+264]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+272]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+280]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+288]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+296]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+304]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+264]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+272]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+280]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+288]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+296]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+304]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+272]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+280]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+288]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+296]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+304]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+280]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+288]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+296]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+304]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+288]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+296]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+304]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+296]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+304]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+304]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+64]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+72]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+64]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+72]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+80]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+72]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+80]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+88]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+64]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+72]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+80]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+88]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+96]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+64]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+72]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+80]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+88]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+96]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+104]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+72]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+80]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+88]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+96]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+104]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+112]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+72]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+80]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+88]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+96]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+104]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+112]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+80]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+88]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+96]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+104]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+112]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+88]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+96]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+104]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+112]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+96]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+104]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+112]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+104]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+112]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov r15d, 1
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov r12, QWORD PTR [rdi+864]
	mov r13, QWORD PTR [rdi+872]
	mov r14, QWORD PTR [rdi+880]
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	sbb r15, r15
	mov rax, QWORD PTR [rdi+832]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+840]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+848]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+856]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+864]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+872]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+880]
	xor r14, rax
	and r14, r15
	xor r14, rax
	mov QWORD PTR [rdi+1712], r8
	mov QWORD PTR [rdi+1720], r9
	mov QWORD PTR [rdi+1728], r10
	mov QWORD PTR [rdi+1736], r11
	mov QWORD PTR [rdi+1744], r12
	mov QWORD PTR [rdi+1752], r13
	mov QWORD PTR [rdi+1760], r14
	mov r15d, 1
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	mov r12, QWORD PTR [rdi+928]
	mov r13, QWORD PTR [rdi+936]
	mov r14, QWORD PTR [rdi+944]
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	sbb r15, r15
	mov rax, QWORD PTR [rdi+896]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+904]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+912]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+920]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+928]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+936]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+944]
	xor r14, rax
	and r14, r15
	xor r14, rax
	mov edx, 0
	mov rax, QWORD PTR [rdi+1712]
	xor rax, r8
	or rdx, rax
	mov rax, QWORD PTR [rdi+1720]
	xor rax, r9
	or rdx, rax
	mov rax, QWORD PTR [rdi+1728]
	xor rax, r10
	or rdx, rax
	mov rax, QWORD PTR [rdi+1736]
	xor rax, r11
	or rdx, rax
	mov rax, QWORD PTR [rdi+1744]
	xor rax, r12
	or rdx, rax
	mov rax, QWORD PTR [rdi+1752]
	xor rax, r13
	or rdx, rax
	mov rax, QWORD PTR [rdi+1760]
	xor rax, r14
	or rdx, rax
	mov rax, QWORD PTR [rdi+1688]
	or rax, rdx
	mov QWORD PTR [rdi+1688], rax
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+320]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+320]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+328]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+320]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+328]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+336]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+320]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+328]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+336]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+344]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+320]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+328]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+336]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+344]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+352]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+320]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+328]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+336]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+344]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+352]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+360]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+320]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+328]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+336]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+344]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+352]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+360]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+368]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+328]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+336]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+344]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+352]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+360]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+368]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+336]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+344]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+352]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+360]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+368]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+344]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+352]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+360]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+368]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+352]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+360]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+368]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+360]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+368]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+368]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+128]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+128]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+136]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+128]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+136]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+144]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+128]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+136]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+144]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+152]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+128]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+136]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+144]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+152]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+160]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+128]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+136]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+144]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+152]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+160]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+168]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+128]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+136]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+144]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+152]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+160]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+168]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+176]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+136]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+144]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+152]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+160]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+168]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+176]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+144]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+152]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+160]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+168]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+176]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+152]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+160]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+168]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+176]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+160]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+168]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+176]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+168]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+176]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+176]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov r15d, 1
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov r12, QWORD PTR [rdi+864]
	mov r13, QWORD PTR [rdi+872]
	mov r14, QWORD PTR [rdi+880]
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	sbb r15, r15
	mov rax, QWORD PTR [rdi+832]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+840]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+848]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+856]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+864]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+872]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+880]
	xor r14, rax
	and r14, r15
	xor r14, rax
	mov QWORD PTR [rdi+1712], r8
	mov QWORD PTR [rdi+1720], r9
	mov QWORD PTR [rdi+1728], r10
	mov QWORD PTR [rdi+1736], r11
	mov QWORD PTR [rdi+1744], r12
	mov QWORD PTR [rdi+1752], r13
	mov QWORD PTR [rdi+1760], r14
	mov r15d, 1
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	mov r12, QWORD PTR [rdi+928]
	mov r13, QWORD PTR [rdi+936]
	mov r14, QWORD PTR [rdi+944]
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	sbb r15, r15
	mov rax, QWORD PTR [rdi+896]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+904]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+912]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+920]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+928]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+936]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+944]
	xor r14, rax
	and r14, r15
	xor r14, rax
	mov edx, 0
	mov rax, QWORD PTR [rdi+1712]
	xor rax, r8
	or rdx, rax
	mov rax, QWORD PTR [rdi+1720]
	xor rax, r9
	or rdx, rax
	mov rax, QWORD PTR [rdi+1728]
	xor rax, r10
	or rdx, rax
	mov rax, QWORD PTR [rdi+1736]
	xor rax, r11
	or rdx, rax
	mov rax, QWORD PTR [rdi+1744]
	xor rax, r12
	or rdx, rax
	mov rax, QWORD PTR [rdi+1752]
	xor rax, r13
	or rdx, rax
	mov rax, QWORD PTR [rdi+1760]
	xor rax, r14
	or rdx, rax
	mov rax, QWORD PTR [rdi+1688]
	or rax, rdx
	mov QWORD PTR [rdi+1688], rax
	mov rdx, QWORD PTR [rdi+1688]
	cmp rdx, 1
	mov edx, 0
	adc rdx, 0
	mov rax, rdx
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6
