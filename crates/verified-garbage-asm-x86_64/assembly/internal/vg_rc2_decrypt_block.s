// The functions of `src/internal/vg_rc2_decrypt_block.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
