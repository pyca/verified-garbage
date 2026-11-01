// The functions of `src/cast5.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_expand_key:
	mov eax, 0
	mov QWORD PTR [rcx+16], rax
	mov QWORD PTR [rcx+24], rax
	mov rax, rcx
	add rax, 16
20:
	movzx r9d, BYTE PTR [rdi]
	mov BYTE PTR [rax], r9b
	add rdi, 1
	add rax, 1
	sub rsi, 1
	jne 20b
	mov esi, 2
21:
	movzx r9d, BYTE PTR [rcx+26]
	movzx eax, BYTE PTR [rcx+24]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+27]
	movzx eax, BYTE PTR [rcx+25]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
22:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 22b
	movdqu XMMWORD PTR [rcx+48], xmm1
	movzx r9d, BYTE PTR [rcx+30]
	movzx eax, BYTE PTR [rcx+28]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+31]
	movzx eax, BYTE PTR [rcx+29]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
23:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 23b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+52]
	mov r9d, DWORD PTR [rcx+16]
	bswap r9d
	xor eax, r9d
	bswap eax
	mov DWORD PTR [rcx+32], eax
	movzx r9d, BYTE PTR [rcx+35]
	movzx eax, BYTE PTR [rcx+33]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+34]
	movzx eax, BYTE PTR [rcx+32]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
24:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 24b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+48]
	mov r9d, DWORD PTR [rcx+24]
	bswap r9d
	xor eax, r9d
	bswap eax
	mov DWORD PTR [rcx+36], eax
	movzx r9d, BYTE PTR [rcx+36]
	movzx eax, BYTE PTR [rcx+37]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+38]
	movzx eax, BYTE PTR [rcx+39]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
25:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 25b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+60]
	mov r9d, DWORD PTR [rcx+28]
	bswap r9d
	xor eax, r9d
	bswap eax
	mov DWORD PTR [rcx+40], eax
	movzx r9d, BYTE PTR [rcx+40]
	movzx eax, BYTE PTR [rcx+43]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+41]
	movzx eax, BYTE PTR [rcx+42]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
26:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 26b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+56]
	mov r9d, DWORD PTR [rcx+20]
	bswap r9d
	xor eax, r9d
	bswap eax
	mov DWORD PTR [rcx+44], eax
	movzx r9d, BYTE PTR [rcx+44]
	movzx eax, BYTE PTR [rcx+41]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+38]
	movzx eax, BYTE PTR [rcx+34]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
27:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 27b
	movdqu XMMWORD PTR [rcx+48], xmm1
	movzx r9d, BYTE PTR [rcx+38]
	movzx eax, BYTE PTR [rcx+39]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+41]
	movzx eax, BYTE PTR [rcx+40]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
28:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 28b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+60]
	mov DWORD PTR [rdx], eax
	movzx r9d, BYTE PTR [rcx+36]
	movzx eax, BYTE PTR [rcx+37]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+43]
	movzx eax, BYTE PTR [rcx+42]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
29:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 29b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+56]
	mov DWORD PTR [rdx+4], eax
	movzx r9d, BYTE PTR [rcx+34]
	movzx eax, BYTE PTR [rcx+35]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+45]
	movzx eax, BYTE PTR [rcx+44]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
210:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 210b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+52]
	mov DWORD PTR [rdx+8], eax
	movzx r9d, BYTE PTR [rcx+32]
	movzx eax, BYTE PTR [rcx+33]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+47]
	movzx eax, BYTE PTR [rcx+46]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
211:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 211b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+48]
	mov DWORD PTR [rdx+12], eax
	movzx r9d, BYTE PTR [rcx+34]
	movzx eax, BYTE PTR [rcx+32]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+35]
	movzx eax, BYTE PTR [rcx+33]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
212:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 212b
	movdqu XMMWORD PTR [rcx+48], xmm1
	movzx r9d, BYTE PTR [rcx+38]
	movzx eax, BYTE PTR [rcx+36]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+39]
	movzx eax, BYTE PTR [rcx+37]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
213:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 213b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+52]
	mov r9d, DWORD PTR [rcx+40]
	bswap r9d
	xor eax, r9d
	bswap eax
	mov DWORD PTR [rcx+16], eax
	movzx r9d, BYTE PTR [rcx+19]
	movzx eax, BYTE PTR [rcx+17]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+18]
	movzx eax, BYTE PTR [rcx+16]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
214:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 214b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+48]
	mov r9d, DWORD PTR [rcx+32]
	bswap r9d
	xor eax, r9d
	bswap eax
	mov DWORD PTR [rcx+20], eax
	movzx r9d, BYTE PTR [rcx+20]
	movzx eax, BYTE PTR [rcx+21]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+22]
	movzx eax, BYTE PTR [rcx+23]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
215:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 215b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+60]
	mov r9d, DWORD PTR [rcx+36]
	bswap r9d
	xor eax, r9d
	bswap eax
	mov DWORD PTR [rcx+24], eax
	movzx r9d, BYTE PTR [rcx+24]
	movzx eax, BYTE PTR [rcx+27]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+25]
	movzx eax, BYTE PTR [rcx+26]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
216:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 216b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+56]
	mov r9d, DWORD PTR [rcx+44]
	bswap r9d
	xor eax, r9d
	bswap eax
	mov DWORD PTR [rcx+28], eax
	movzx r9d, BYTE PTR [rcx+23]
	movzx eax, BYTE PTR [rcx+19]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+29]
	movzx eax, BYTE PTR [rcx+24]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
217:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 217b
	movdqu XMMWORD PTR [rcx+48], xmm1
	movzx r9d, BYTE PTR [rcx+29]
	movzx eax, BYTE PTR [rcx+28]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+18]
	movzx eax, BYTE PTR [rcx+19]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
218:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 218b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+60]
	mov DWORD PTR [rdx+16], eax
	movzx r9d, BYTE PTR [rcx+31]
	movzx eax, BYTE PTR [rcx+30]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+16]
	movzx eax, BYTE PTR [rcx+17]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
219:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 219b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+56]
	mov DWORD PTR [rdx+20], eax
	movzx r9d, BYTE PTR [rcx+25]
	movzx eax, BYTE PTR [rcx+24]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+22]
	movzx eax, BYTE PTR [rcx+23]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
220:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 220b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+52]
	mov DWORD PTR [rdx+24], eax
	movzx r9d, BYTE PTR [rcx+27]
	movzx eax, BYTE PTR [rcx+26]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+20]
	movzx eax, BYTE PTR [rcx+21]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
221:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 221b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+48]
	mov DWORD PTR [rdx+28], eax
	movzx r9d, BYTE PTR [rcx+26]
	movzx eax, BYTE PTR [rcx+24]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+27]
	movzx eax, BYTE PTR [rcx+25]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
222:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 222b
	movdqu XMMWORD PTR [rcx+48], xmm1
	movzx r9d, BYTE PTR [rcx+30]
	movzx eax, BYTE PTR [rcx+28]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+31]
	movzx eax, BYTE PTR [rcx+29]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
223:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 223b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+52]
	mov r9d, DWORD PTR [rcx+16]
	bswap r9d
	xor eax, r9d
	bswap eax
	mov DWORD PTR [rcx+32], eax
	movzx r9d, BYTE PTR [rcx+35]
	movzx eax, BYTE PTR [rcx+33]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+34]
	movzx eax, BYTE PTR [rcx+32]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
224:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 224b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+48]
	mov r9d, DWORD PTR [rcx+24]
	bswap r9d
	xor eax, r9d
	bswap eax
	mov DWORD PTR [rcx+36], eax
	movzx r9d, BYTE PTR [rcx+36]
	movzx eax, BYTE PTR [rcx+37]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+38]
	movzx eax, BYTE PTR [rcx+39]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
225:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 225b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+60]
	mov r9d, DWORD PTR [rcx+28]
	bswap r9d
	xor eax, r9d
	bswap eax
	mov DWORD PTR [rcx+40], eax
	movzx r9d, BYTE PTR [rcx+40]
	movzx eax, BYTE PTR [rcx+43]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+41]
	movzx eax, BYTE PTR [rcx+42]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
226:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 226b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+56]
	mov r9d, DWORD PTR [rcx+20]
	bswap r9d
	xor eax, r9d
	bswap eax
	mov DWORD PTR [rcx+44], eax
	movzx r9d, BYTE PTR [rcx+38]
	movzx eax, BYTE PTR [rcx+34]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+44]
	movzx eax, BYTE PTR [rcx+41]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
227:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 227b
	movdqu XMMWORD PTR [rcx+48], xmm1
	movzx r9d, BYTE PTR [rcx+45]
	movzx eax, BYTE PTR [rcx+44]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+34]
	movzx eax, BYTE PTR [rcx+35]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
228:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 228b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+60]
	mov DWORD PTR [rdx+32], eax
	movzx r9d, BYTE PTR [rcx+47]
	movzx eax, BYTE PTR [rcx+46]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+32]
	movzx eax, BYTE PTR [rcx+33]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
229:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 229b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+56]
	mov DWORD PTR [rdx+36], eax
	movzx r9d, BYTE PTR [rcx+41]
	movzx eax, BYTE PTR [rcx+40]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+38]
	movzx eax, BYTE PTR [rcx+39]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
230:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 230b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+52]
	mov DWORD PTR [rdx+40], eax
	movzx r9d, BYTE PTR [rcx+43]
	movzx eax, BYTE PTR [rcx+42]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+36]
	movzx eax, BYTE PTR [rcx+37]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
231:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 231b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+48]
	mov DWORD PTR [rdx+44], eax
	movzx r9d, BYTE PTR [rcx+34]
	movzx eax, BYTE PTR [rcx+32]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+35]
	movzx eax, BYTE PTR [rcx+33]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
232:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 232b
	movdqu XMMWORD PTR [rcx+48], xmm1
	movzx r9d, BYTE PTR [rcx+38]
	movzx eax, BYTE PTR [rcx+36]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+39]
	movzx eax, BYTE PTR [rcx+37]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
233:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 233b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+52]
	mov r9d, DWORD PTR [rcx+40]
	bswap r9d
	xor eax, r9d
	bswap eax
	mov DWORD PTR [rcx+16], eax
	movzx r9d, BYTE PTR [rcx+19]
	movzx eax, BYTE PTR [rcx+17]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+18]
	movzx eax, BYTE PTR [rcx+16]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
234:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 234b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+48]
	mov r9d, DWORD PTR [rcx+32]
	bswap r9d
	xor eax, r9d
	bswap eax
	mov DWORD PTR [rcx+20], eax
	movzx r9d, BYTE PTR [rcx+20]
	movzx eax, BYTE PTR [rcx+21]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+22]
	movzx eax, BYTE PTR [rcx+23]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
235:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 235b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+60]
	mov r9d, DWORD PTR [rcx+36]
	bswap r9d
	xor eax, r9d
	bswap eax
	mov DWORD PTR [rcx+24], eax
	movzx r9d, BYTE PTR [rcx+24]
	movzx eax, BYTE PTR [rcx+27]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+25]
	movzx eax, BYTE PTR [rcx+26]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
236:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 236b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+56]
	mov r9d, DWORD PTR [rcx+44]
	bswap r9d
	xor eax, r9d
	bswap eax
	mov DWORD PTR [rcx+28], eax
	movzx r9d, BYTE PTR [rcx+29]
	movzx eax, BYTE PTR [rcx+24]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+23]
	movzx eax, BYTE PTR [rcx+19]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
237:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 237b
	movdqu XMMWORD PTR [rcx+48], xmm1
	movzx r9d, BYTE PTR [rcx+22]
	movzx eax, BYTE PTR [rcx+23]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+25]
	movzx eax, BYTE PTR [rcx+24]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
238:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 238b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+60]
	mov DWORD PTR [rdx+48], eax
	movzx r9d, BYTE PTR [rcx+20]
	movzx eax, BYTE PTR [rcx+21]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+27]
	movzx eax, BYTE PTR [rcx+26]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
239:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 239b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+56]
	mov DWORD PTR [rdx+52], eax
	movzx r9d, BYTE PTR [rcx+18]
	movzx eax, BYTE PTR [rcx+19]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+29]
	movzx eax, BYTE PTR [rcx+28]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
240:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 240b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+52]
	mov DWORD PTR [rdx+56], eax
	movzx r9d, BYTE PTR [rcx+16]
	movzx eax, BYTE PTR [rcx+17]
	shl rax, 32
	or r9, rax
	movzx r10d, BYTE PTR [rcx+31]
	movzx eax, BYTE PTR [rcx+30]
	shl rax, 32
	or rax, r10
	movq xmm0, r9
	movq xmm4, rax
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S5678}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
241:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 241b
	movdqu XMMWORD PTR [rcx], xmm1
	mov eax, DWORD PTR [rcx]
	xor eax, DWORD PTR [rcx+4]
	xor eax, DWORD PTR [rcx+8]
	xor eax, DWORD PTR [rcx+12]
	xor eax, DWORD PTR [rcx+48]
	mov DWORD PTR [rdx+60], eax
	add rdx, 64
	sub rsi, 1
	jne 21b
	ret
	.p2align 6

vg_cast5_ecb_encrypt:
	mov QWORD PTR [r8+16], rbx
	mov QWORD PTR [r8+24], rbp
	mov QWORD PTR [r8+32], r12
	mov QWORD PTR [r8+40], r13
	mov QWORD PTR [r8+48], r14
	mov QWORD PTR [r8+56], r15
	test rcx, rcx
	je 20f
22:
	mov ebx, DWORD PTR [rdx]
	bswap ebx
	mov ebp, DWORD PTR [rdx+4]
	bswap ebp
	mov r12, rdi
	mov r13, rsi
	shr r13, 2
	add r13, 1
	cmp rsi, 16
23:
	mov eax, DWORD PTR [r12]
	add eax, ebp
	mov r9d, DWORD PTR [r12+64]
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 31
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 30
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 28
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 24
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 16
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	mov r9d, eax
	and r9d, 255
	mov r14d, eax
	shr r14d, 8
	and r14d, 255
	shl r14, 32
	or r9, r14
	movq xmm0, r9
	mov r9d, eax
	shr r9d, 16
	and r9d, 255
	mov r14d, eax
	shr r14d, 24
	shl r14, 32
	or r9, r14
	movq xmm4, r9
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S1234}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
24:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 24b
	movdqu XMMWORD PTR [r8], xmm1
	mov eax, DWORD PTR [r8+12]
	xor eax, DWORD PTR [r8+8]
	sub eax, DWORD PTR [r8+4]
	add eax, DWORD PTR [r8]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	add r12, 4
	mov eax, DWORD PTR [r12]
	xor eax, ebp
	mov r9d, DWORD PTR [r12+64]
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 31
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 30
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 28
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 24
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 16
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	mov r9d, eax
	and r9d, 255
	mov r14d, eax
	shr r14d, 8
	and r14d, 255
	shl r14, 32
	or r9, r14
	movq xmm0, r9
	mov r9d, eax
	shr r9d, 16
	and r9d, 255
	mov r14d, eax
	shr r14d, 24
	shl r14, 32
	or r9, r14
	movq xmm4, r9
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S1234}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
25:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 25b
	movdqu XMMWORD PTR [r8], xmm1
	mov eax, DWORD PTR [r8+12]
	sub eax, DWORD PTR [r8+8]
	add eax, DWORD PTR [r8+4]
	xor eax, DWORD PTR [r8]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	add r12, 4
	mov eax, DWORD PTR [r12]
	sub eax, ebp
	mov r9d, DWORD PTR [r12+64]
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 31
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 30
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 28
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 24
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 16
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	mov r9d, eax
	and r9d, 255
	mov r14d, eax
	shr r14d, 8
	and r14d, 255
	shl r14, 32
	or r9, r14
	movq xmm0, r9
	mov r9d, eax
	shr r9d, 16
	and r9d, 255
	mov r14d, eax
	shr r14d, 24
	shl r14, 32
	or r9, r14
	movq xmm4, r9
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S1234}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
26:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 26b
	movdqu XMMWORD PTR [r8], xmm1
	mov eax, DWORD PTR [r8+12]
	add eax, DWORD PTR [r8+8]
	xor eax, DWORD PTR [r8+4]
	sub eax, DWORD PTR [r8]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	add r12, 4
	sub r13, 1
	jne 23b
	cmp rsi, 16
	je 27f
	jmp 28f
27:
	mov eax, DWORD PTR [r12]
	add eax, ebp
	mov r9d, DWORD PTR [r12+64]
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 31
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 30
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 28
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 24
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 16
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	mov r9d, eax
	and r9d, 255
	mov r14d, eax
	shr r14d, 8
	and r14d, 255
	shl r14, 32
	or r9, r14
	movq xmm0, r9
	mov r9d, eax
	shr r9d, 16
	and r9d, 255
	mov r14d, eax
	shr r14d, 24
	shl r14, 32
	or r9, r14
	movq xmm4, r9
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S1234}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
29:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 29b
	movdqu XMMWORD PTR [r8], xmm1
	mov eax, DWORD PTR [r8+12]
	xor eax, DWORD PTR [r8+8]
	sub eax, DWORD PTR [r8+4]
	add eax, DWORD PTR [r8]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	add r12, 4
28:
	bswap ebp
	mov DWORD PTR [rdx], ebp
	bswap ebx
	mov DWORD PTR [rdx+4], ebx
	add rdx, 8
	sub rcx, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r8+16]
	mov rbp, QWORD PTR [r8+24]
	mov r12, QWORD PTR [r8+32]
	mov r13, QWORD PTR [r8+40]
	mov r14, QWORD PTR [r8+48]
	mov r15, QWORD PTR [r8+56]
	ret
	.p2align 6

vg_cast5_ecb_decrypt:
	mov QWORD PTR [r8+16], rbx
	mov QWORD PTR [r8+24], rbp
	mov QWORD PTR [r8+32], r12
	mov QWORD PTR [r8+40], r13
	mov QWORD PTR [r8+48], r14
	mov QWORD PTR [r8+56], r15
	test rcx, rcx
	je 20f
22:
	mov ebx, DWORD PTR [rdx]
	bswap ebx
	mov ebp, DWORD PTR [rdx+4]
	bswap ebp
	mov r12, rsi
	shl r12, 2
	add r12, rdi
	sub r12, 4
	mov r13, rsi
	shr r13, 2
	add r13, 1
	cmp rsi, 16
	je 23f
	jmp 24f
23:
	mov eax, DWORD PTR [r12]
	add eax, ebp
	mov r9d, DWORD PTR [r12+64]
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 31
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 30
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 28
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 24
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 16
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	mov r9d, eax
	and r9d, 255
	mov r14d, eax
	shr r14d, 8
	and r14d, 255
	shl r14, 32
	or r9, r14
	movq xmm0, r9
	mov r9d, eax
	shr r9d, 16
	and r9d, 255
	mov r14d, eax
	shr r14d, 24
	shl r14, 32
	or r9, r14
	movq xmm4, r9
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S1234}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
25:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 25b
	movdqu XMMWORD PTR [r8], xmm1
	mov eax, DWORD PTR [r8+12]
	xor eax, DWORD PTR [r8+8]
	sub eax, DWORD PTR [r8+4]
	add eax, DWORD PTR [r8]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	sub r12, 4
24:
26:
	mov eax, DWORD PTR [r12]
	sub eax, ebp
	mov r9d, DWORD PTR [r12+64]
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 31
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 30
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 28
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 24
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 16
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	mov r9d, eax
	and r9d, 255
	mov r14d, eax
	shr r14d, 8
	and r14d, 255
	shl r14, 32
	or r9, r14
	movq xmm0, r9
	mov r9d, eax
	shr r9d, 16
	and r9d, 255
	mov r14d, eax
	shr r14d, 24
	shl r14, 32
	or r9, r14
	movq xmm4, r9
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S1234}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
27:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 27b
	movdqu XMMWORD PTR [r8], xmm1
	mov eax, DWORD PTR [r8+12]
	add eax, DWORD PTR [r8+8]
	xor eax, DWORD PTR [r8+4]
	sub eax, DWORD PTR [r8]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	sub r12, 4
	mov eax, DWORD PTR [r12]
	xor eax, ebp
	mov r9d, DWORD PTR [r12+64]
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 31
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 30
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 28
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 24
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 16
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	mov r9d, eax
	and r9d, 255
	mov r14d, eax
	shr r14d, 8
	and r14d, 255
	shl r14, 32
	or r9, r14
	movq xmm0, r9
	mov r9d, eax
	shr r9d, 16
	and r9d, 255
	mov r14d, eax
	shr r14d, 24
	shl r14, 32
	or r9, r14
	movq xmm4, r9
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S1234}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
28:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 28b
	movdqu XMMWORD PTR [r8], xmm1
	mov eax, DWORD PTR [r8+12]
	sub eax, DWORD PTR [r8+8]
	add eax, DWORD PTR [r8+4]
	xor eax, DWORD PTR [r8]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	sub r12, 4
	mov eax, DWORD PTR [r12]
	add eax, ebp
	mov r9d, DWORD PTR [r12+64]
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 31
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 30
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 28
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 24
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 16
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	mov r9d, eax
	and r9d, 255
	mov r14d, eax
	shr r14d, 8
	and r14d, 255
	shl r14, 32
	or r9, r14
	movq xmm0, r9
	mov r9d, eax
	shr r9d, 16
	and r9d, 255
	mov r14d, eax
	shr r14d, 24
	shl r14, 32
	or r9, r14
	movq xmm4, r9
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S1234}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
29:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 29b
	movdqu XMMWORD PTR [r8], xmm1
	mov eax, DWORD PTR [r8+12]
	xor eax, DWORD PTR [r8+8]
	sub eax, DWORD PTR [r8+4]
	add eax, DWORD PTR [r8]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	sub r12, 4
	sub r13, 1
	jne 26b
	bswap ebp
	mov DWORD PTR [rdx], ebp
	bswap ebx
	mov DWORD PTR [rdx+4], ebx
	add rdx, 8
	sub rcx, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r8+16]
	mov rbp, QWORD PTR [r8+24]
	mov r12, QWORD PTR [r8+32]
	mov r13, QWORD PTR [r8+40]
	mov r14, QWORD PTR [r8+48]
	mov r15, QWORD PTR [r8+56]
	ret
	.p2align 6
