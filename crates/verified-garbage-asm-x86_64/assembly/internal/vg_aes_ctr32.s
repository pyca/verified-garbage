// The functions of `src/internal/vg_aes_ctr32.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr32:
	mov r11, rcx
	test r8, r8
	je 20f
	movabs rax, 6148914691236517205
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+144], xmm0
	movabs rax, 3689348814741910323
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+160], xmm0
	movabs rax, 1085102592571150095
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+176], xmm0
	movabs rax, 71777214294589695
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+192], xmm0
	movabs rax, 281470681808895
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+208], xmm0
	movabs rax, 4294967295
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+224], xmm0
	movabs rax, 71776119077928960
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+240], xmm0
	movabs rax, 71777214277877760
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+256], xmm0
	movabs rax, -281470681808896
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+272], xmm0
	mov r10, rdi
	mov rax, r9
	add rax, 416
	mov rdi, rsi
	shr rdi, 1
22:
	movdqu xmm0, XMMWORD PTR [r10]
	movdqu xmm1, XMMWORD PTR [r10+16]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm4, xmm1
	movdqu xmm9, XMMWORD PTR [r9+192]
	movdqa xmm8, xmm0
	psrlq xmm8, 8
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 8
	pxor xmm0, xmm8
	movdqu xmm9, XMMWORD PTR [r9+208]
	movdqa xmm8, xmm0
	psrlq xmm8, 16
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 16
	pxor xmm0, xmm8
	movdqu xmm9, XMMWORD PTR [r9+224]
	movdqa xmm8, xmm0
	psrlq xmm8, 32
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 32
	pxor xmm0, xmm8
	movdqu xmm9, XMMWORD PTR [r9+176]
	movdqa xmm8, xmm0
	psrlq xmm8, 4
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 4
	pxor xmm0, xmm8
	movdqa xmm1, xmm0
	movdqa xmm5, xmm4
	movdqu xmm10, XMMWORD PTR [r9+256]
	movdqu xmm11, XMMWORD PTR [r9+272]
	movdqa xmm8, xmm1
	psrlw xmm8, 8
	pxor xmm8, xmm1
	pand xmm8, xmm10
	pxor xmm1, xmm8
	psllw xmm8, 8
	pxor xmm1, xmm8
	movdqa xmm8, xmm1
	psllw xmm8, 4
	movdqa xmm9, xmm1
	psrlw xmm9, 12
	pxor xmm8, xmm9
	pxor xmm8, xmm1
	pand xmm8, xmm11
	pxor xmm1, xmm8
	movdqa xmm8, xmm5
	psrlw xmm8, 8
	pxor xmm8, xmm5
	pand xmm8, xmm10
	pxor xmm5, xmm8
	psllw xmm8, 8
	pxor xmm5, xmm8
	movdqa xmm8, xmm5
	psllw xmm8, 4
	movdqa xmm9, xmm5
	psrlw xmm9, 12
	pxor xmm8, xmm9
	pxor xmm8, xmm5
	pand xmm8, xmm11
	pxor xmm5, xmm8
	punpckhqdq xmm1, xmm1
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm5, xmm5
	punpcklqdq xmm4, xmm5
	movdqa xmm2, xmm0
	movdqu xmm9, XMMWORD PTR [r9+160]
	movdqa xmm8, xmm0
	psrlq xmm8, 2
	pxor xmm8, xmm2
	pand xmm8, xmm9
	pxor xmm2, xmm8
	psllq xmm8, 2
	pxor xmm0, xmm8
	movdqa xmm6, xmm4
	movdqa xmm8, xmm4
	psrlq xmm8, 2
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 2
	pxor xmm4, xmm8
	movdqa xmm1, xmm0
	movdqa xmm3, xmm2
	movdqa xmm5, xmm4
	movdqa xmm7, xmm6
	movdqu xmm9, XMMWORD PTR [r9+144]
	movdqa xmm8, xmm0
	psrlq xmm8, 1
	pxor xmm8, xmm1
	pand xmm8, xmm9
	pxor xmm1, xmm8
	psllq xmm8, 1
	pxor xmm0, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 1
	pxor xmm8, xmm3
	pand xmm8, xmm9
	pxor xmm3, xmm8
	psllq xmm8, 1
	pxor xmm2, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 1
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 1
	pxor xmm4, xmm8
	movdqa xmm8, xmm6
	psrlq xmm8, 1
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 1
	pxor xmm6, xmm8
	movdqa xmm8, xmm0
	punpcklqdq xmm8, xmm1
	movdqu XMMWORD PTR [rax], xmm8
	movdqa xmm8, xmm2
	punpcklqdq xmm8, xmm3
	movdqu XMMWORD PTR [rax+16], xmm8
	movdqa xmm8, xmm4
	punpcklqdq xmm8, xmm5
	movdqu XMMWORD PTR [rax+32], xmm8
	movdqa xmm8, xmm6
	punpcklqdq xmm8, xmm7
	movdqu XMMWORD PTR [rax+48], xmm8
	punpckhqdq xmm0, xmm1
	movdqu XMMWORD PTR [rax+64], xmm0
	punpckhqdq xmm2, xmm3
	movdqu XMMWORD PTR [rax+80], xmm2
	punpckhqdq xmm4, xmm5
	movdqu XMMWORD PTR [rax+96], xmm4
	punpckhqdq xmm6, xmm7
	movdqu XMMWORD PTR [rax+112], xmm6
	add r10, 32
	add rax, 128
	sub rdi, 1
	jne 22b
	movdqu xmm0, XMMWORD PTR [r10]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm0
	punpckhqdq xmm4, xmm4
	movdqu xmm9, XMMWORD PTR [r9+192]
	movdqa xmm8, xmm0
	psrlq xmm8, 8
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 8
	pxor xmm0, xmm8
	movdqu xmm9, XMMWORD PTR [r9+208]
	movdqa xmm8, xmm0
	psrlq xmm8, 16
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 16
	pxor xmm0, xmm8
	movdqu xmm9, XMMWORD PTR [r9+224]
	movdqa xmm8, xmm0
	psrlq xmm8, 32
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 32
	pxor xmm0, xmm8
	movdqu xmm9, XMMWORD PTR [r9+176]
	movdqa xmm8, xmm0
	psrlq xmm8, 4
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 4
	pxor xmm0, xmm8
	movdqa xmm1, xmm0
	movdqa xmm5, xmm4
	movdqu xmm10, XMMWORD PTR [r9+256]
	movdqu xmm11, XMMWORD PTR [r9+272]
	movdqa xmm8, xmm1
	psrlw xmm8, 8
	pxor xmm8, xmm1
	pand xmm8, xmm10
	pxor xmm1, xmm8
	psllw xmm8, 8
	pxor xmm1, xmm8
	movdqa xmm8, xmm1
	psllw xmm8, 4
	movdqa xmm9, xmm1
	psrlw xmm9, 12
	pxor xmm8, xmm9
	pxor xmm8, xmm1
	pand xmm8, xmm11
	pxor xmm1, xmm8
	movdqa xmm8, xmm5
	psrlw xmm8, 8
	pxor xmm8, xmm5
	pand xmm8, xmm10
	pxor xmm5, xmm8
	psllw xmm8, 8
	pxor xmm5, xmm8
	movdqa xmm8, xmm5
	psllw xmm8, 4
	movdqa xmm9, xmm5
	psrlw xmm9, 12
	pxor xmm8, xmm9
	pxor xmm8, xmm5
	pand xmm8, xmm11
	pxor xmm5, xmm8
	punpckhqdq xmm1, xmm1
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm5, xmm5
	punpcklqdq xmm4, xmm5
	movdqa xmm2, xmm0
	movdqu xmm9, XMMWORD PTR [r9+160]
	movdqa xmm8, xmm0
	psrlq xmm8, 2
	pxor xmm8, xmm2
	pand xmm8, xmm9
	pxor xmm2, xmm8
	psllq xmm8, 2
	pxor xmm0, xmm8
	movdqa xmm6, xmm4
	movdqa xmm8, xmm4
	psrlq xmm8, 2
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 2
	pxor xmm4, xmm8
	movdqa xmm1, xmm0
	movdqa xmm3, xmm2
	movdqa xmm5, xmm4
	movdqa xmm7, xmm6
	movdqu xmm9, XMMWORD PTR [r9+144]
	movdqa xmm8, xmm0
	psrlq xmm8, 1
	pxor xmm8, xmm1
	pand xmm8, xmm9
	pxor xmm1, xmm8
	psllq xmm8, 1
	pxor xmm0, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 1
	pxor xmm8, xmm3
	pand xmm8, xmm9
	pxor xmm3, xmm8
	psllq xmm8, 1
	pxor xmm2, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 1
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 1
	pxor xmm4, xmm8
	movdqa xmm8, xmm6
	psrlq xmm8, 1
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 1
	pxor xmm6, xmm8
	movdqa xmm8, xmm0
	punpcklqdq xmm8, xmm1
	movdqu XMMWORD PTR [rax], xmm8
	movdqa xmm8, xmm2
	punpcklqdq xmm8, xmm3
	movdqu XMMWORD PTR [rax+16], xmm8
	movdqa xmm8, xmm4
	punpcklqdq xmm8, xmm5
	movdqu XMMWORD PTR [rax+32], xmm8
	movdqa xmm8, xmm6
	punpcklqdq xmm8, xmm7
	movdqu XMMWORD PTR [rax+48], xmm8
	mov rax, r9
	add rax, 480
	mov rdi, rsi
23:
	mov r10, QWORD PTR [rax]
	xor r10, -1
	mov QWORD PTR [rax], r10
	mov r10, QWORD PTR [rax+8]
	xor r10, -1
	mov QWORD PTR [rax+8], r10
	mov r10, QWORD PTR [rax+40]
	xor r10, -1
	mov QWORD PTR [rax+40], r10
	mov r10, QWORD PTR [rax+48]
	xor r10, -1
	mov QWORD PTR [rax+48], r10
	add rax, 64
	sub rdi, 1
	jne 23b
24:
	movdqu xmm0, XMMWORD PTR [rdx]
	mov eax, DWORD PTR [rdx+12]
	bswap eax
	movdqu XMMWORD PTR [r9+288], xmm0
	mov r10d, eax
	add r10d, 0
	bswap r10d
	mov DWORD PTR [r9+300], r10d
	movdqu XMMWORD PTR [r9+304], xmm0
	mov r10d, eax
	add r10d, 1
	bswap r10d
	mov DWORD PTR [r9+316], r10d
	movdqu XMMWORD PTR [r9+320], xmm0
	mov r10d, eax
	add r10d, 2
	bswap r10d
	mov DWORD PTR [r9+332], r10d
	movdqu XMMWORD PTR [r9+336], xmm0
	mov r10d, eax
	add r10d, 3
	bswap r10d
	mov DWORD PTR [r9+348], r10d
	movdqu XMMWORD PTR [r9+352], xmm0
	mov r10d, eax
	add r10d, 4
	bswap r10d
	mov DWORD PTR [r9+364], r10d
	movdqu XMMWORD PTR [r9+368], xmm0
	mov r10d, eax
	add r10d, 5
	bswap r10d
	mov DWORD PTR [r9+380], r10d
	movdqu XMMWORD PTR [r9+384], xmm0
	mov r10d, eax
	add r10d, 6
	bswap r10d
	mov DWORD PTR [r9+396], r10d
	movdqu XMMWORD PTR [r9+400], xmm0
	mov r10d, eax
	add r10d, 7
	bswap r10d
	mov DWORD PTR [r9+412], r10d
	movdqu xmm0, XMMWORD PTR [r9+288]
	movdqu xmm8, XMMWORD PTR [r9+352]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm8
	punpckhqdq xmm4, xmm8
	movdqu xmm1, XMMWORD PTR [r9+304]
	movdqu xmm8, XMMWORD PTR [r9+368]
	movdqa xmm5, xmm1
	punpcklqdq xmm1, xmm8
	punpckhqdq xmm5, xmm8
	movdqu xmm2, XMMWORD PTR [r9+320]
	movdqu xmm8, XMMWORD PTR [r9+384]
	movdqa xmm6, xmm2
	punpcklqdq xmm2, xmm8
	punpckhqdq xmm6, xmm8
	movdqu xmm3, XMMWORD PTR [r9+336]
	movdqu xmm8, XMMWORD PTR [r9+400]
	movdqa xmm7, xmm3
	punpcklqdq xmm3, xmm8
	punpckhqdq xmm7, xmm8
	movdqu xmm9, XMMWORD PTR [r9+192]
	movdqa xmm8, xmm0
	psrlq xmm8, 8
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 8
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 8
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 8
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 8
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 8
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 8
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 8
	pxor xmm3, xmm8
	movdqu xmm9, XMMWORD PTR [r9+208]
	movdqa xmm8, xmm0
	psrlq xmm8, 16
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 16
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 16
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 16
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 16
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 16
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 16
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 16
	pxor xmm3, xmm8
	movdqu xmm9, XMMWORD PTR [r9+224]
	movdqa xmm8, xmm0
	psrlq xmm8, 32
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 32
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 32
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 32
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 32
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 32
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 32
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 32
	pxor xmm3, xmm8
	movdqu xmm9, XMMWORD PTR [r9+176]
	movdqa xmm8, xmm0
	psrlq xmm8, 4
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 4
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 4
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 4
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 4
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 4
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 4
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 4
	pxor xmm3, xmm8
	movdqu xmm9, XMMWORD PTR [r9+160]
	movdqa xmm8, xmm0
	psrlq xmm8, 2
	pxor xmm8, xmm2
	pand xmm8, xmm9
	pxor xmm2, xmm8
	psllq xmm8, 2
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 2
	pxor xmm8, xmm3
	pand xmm8, xmm9
	pxor xmm3, xmm8
	psllq xmm8, 2
	pxor xmm1, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 2
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 2
	pxor xmm4, xmm8
	movdqa xmm8, xmm5
	psrlq xmm8, 2
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 2
	pxor xmm5, xmm8
	movdqu xmm9, XMMWORD PTR [r9+144]
	movdqa xmm8, xmm0
	psrlq xmm8, 1
	pxor xmm8, xmm1
	pand xmm8, xmm9
	pxor xmm1, xmm8
	psllq xmm8, 1
	pxor xmm0, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 1
	pxor xmm8, xmm3
	pand xmm8, xmm9
	pxor xmm3, xmm8
	psllq xmm8, 1
	pxor xmm2, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 1
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 1
	pxor xmm4, xmm8
	movdqa xmm8, xmm6
	psrlq xmm8, 1
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 1
	pxor xmm6, xmm8
	mov r10, rsi
	shr r10, 1
	sub r10, 1
	mov rax, r9
	add rax, 416
	movdqu xmm8, XMMWORD PTR [rax]
	pshufd xmm9, xmm8, 68
	pshufd xmm8, xmm8, 238
	pxor xmm0, xmm9
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rax+16]
	pshufd xmm9, xmm8, 68
	pshufd xmm8, xmm8, 238
	pxor xmm2, xmm9
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rax+32]
	pshufd xmm9, xmm8, 68
	pshufd xmm8, xmm8, 238
	pxor xmm4, xmm9
	pxor xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rax+48]
	pshufd xmm9, xmm8, 68
	pshufd xmm8, xmm8, 238
	pxor xmm6, xmm9
	pxor xmm7, xmm8
	add rax, 64
25:
	pxor xmm2, xmm5
	movdqa xmm8, xmm2
	pxor xmm8, xmm1
	movdqa xmm9, xmm8
	pxor xmm9, xmm6
	pxor xmm3, xmm9
	pxor xmm3, xmm7
	pxor xmm0, xmm8
	movdqa xmm10, xmm3
	pxor xmm10, xmm2
	movdqa xmm11, xmm10
	pxor xmm11, xmm0
	pxor xmm5, xmm11
	movdqa xmm12, xmm5
	pxor xmm12, xmm7
	movdqa xmm13, xmm11
	pxor xmm13, xmm9
	movdqa xmm14, xmm11
	pxor xmm14, xmm4
	movdqa xmm15, xmm14
	pand xmm15, xmm11
	movdqu XMMWORD PTR [r9], xmm11
	movdqa xmm11, xmm14
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r9+16], xmm5
	movdqa xmm5, xmm14
	pxor xmm5, xmm3
	pxor xmm3, xmm4
	movdqu XMMWORD PTR [r9+32], xmm14
	movdqa xmm14, xmm12
	pand xmm14, xmm9
	movdqu XMMWORD PTR [r9+48], xmm9
	movdqa xmm9, xmm11
	pand xmm9, xmm13
	movdqu XMMWORD PTR [r9+64], xmm11
	movdqa xmm11, xmm12
	pxor xmm11, xmm6
	pxor xmm4, xmm10
	movdqu XMMWORD PTR [r9+80], xmm12
	movdqa xmm12, xmm4
	pand xmm12, xmm5
	pxor xmm9, xmm12
	movdqu XMMWORD PTR [r9+96], xmm5
	movdqa xmm5, xmm7
	pand xmm5, xmm8
	pxor xmm12, xmm14
	pxor xmm5, xmm15
	pxor xmm5, xmm12
	movdqa xmm14, xmm0
	pxor xmm14, xmm7
	pxor xmm1, xmm4
	pxor xmm5, xmm11
	movdqa xmm11, xmm0
	pand xmm11, xmm3
	pxor xmm12, xmm11
	movdqu XMMWORD PTR [r9+112], xmm0
	movdqa xmm0, xmm14
	pand xmm0, xmm1
	pxor xmm0, xmm9
	pxor xmm0, xmm15
	pxor xmm0, xmm2
	movdqu xmm15, XMMWORD PTR [r9+16]
	movdqa xmm2, xmm15
	pand xmm2, xmm6
	movdqu XMMWORD PTR [r9+128], xmm6
	movdqa xmm6, xmm15
	pxor xmm6, xmm8
	pxor xmm12, xmm2
	pxor xmm12, xmm6
	movdqa xmm2, xmm4
	pxor xmm2, xmm15
	movdqa xmm6, xmm13
	pxor xmm6, xmm1
	movdqa xmm15, xmm2
	pand xmm15, xmm6
	pxor xmm9, xmm15
	pxor xmm9, xmm11
	movdqa xmm15, xmm5
	pand xmm15, xmm0
	pxor xmm9, xmm10
	movdqa xmm11, xmm12
	pxor xmm11, xmm15
	pxor xmm15, xmm9
	movdqa xmm10, xmm0
	pxor xmm10, xmm9
	pand xmm11, xmm10
	pxor xmm5, xmm12
	pxor xmm11, xmm9
	pxor xmm0, xmm11
	movdqa xmm10, xmm15
	pxor xmm10, xmm11
	pand xmm9, xmm10
	pxor xmm0, xmm9
	pand xmm8, xmm11
	pxor xmm9, xmm15
	pand xmm15, xmm5
	pxor xmm12, xmm15
	pand xmm9, xmm12
	pxor xmm9, xmm5
	movdqu xmm10, XMMWORD PTR [r9+64]
	pand xmm10, xmm9
	pand xmm7, xmm11
	movdqa xmm15, xmm12
	pxor xmm15, xmm9
	pand xmm6, xmm15
	pand xmm1, xmm12
	pand xmm14, xmm12
	pand xmm13, xmm9
	pxor xmm12, xmm11
	pxor xmm6, xmm13
	pand xmm15, xmm2
	pxor xmm13, xmm1
	pand xmm3, xmm12
	pxor xmm11, xmm0
	pxor xmm9, xmm0
	movdqu xmm5, XMMWORD PTR [r9+112]
	pand xmm5, xmm12
	movdqu xmm2, XMMWORD PTR [r9+48]
	pand xmm2, xmm0
	pxor xmm2, xmm8
	pxor xmm5, xmm15
	pxor xmm3, xmm6
	pxor xmm12, xmm9
	movdqu xmm1, XMMWORD PTR [r9+80]
	pand xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r9+96]
	pand xmm1, xmm12
	pxor xmm15, xmm7
	pand xmm12, xmm4
	pxor xmm6, xmm1
	movdqu xmm4, XMMWORD PTR [r9+32]
	pand xmm4, xmm9
	pxor xmm13, xmm2
	pxor xmm12, xmm10
	pxor xmm4, xmm12
	pxor xmm5, xmm12
	pxor xmm5, xmm13
	pxor xmm15, xmm4
	pxor xmm4, xmm14
	pxor xmm14, xmm5
	pxor xmm6, xmm8
	movdqu xmm12, XMMWORD PTR [r9+16]
	pand xmm12, xmm11
	pxor xmm1, xmm4
	pxor xmm14, xmm0
	pxor xmm13, xmm4
	movdqu xmm8, XMMWORD PTR [r9+128]
	pand xmm11, xmm8
	pxor xmm14, xmm10
	pxor xmm2, xmm1
	pxor xmm6, xmm11
	movdqu xmm0, XMMWORD PTR [r9]
	pand xmm9, xmm0
	pxor xmm2, xmm9
	pxor xmm14, xmm7
	pxor xmm15, xmm12
	pxor xmm1, xmm15
	pxor xmm6, xmm9
	pxor xmm1, xmm3
	movdqa xmm8, xmm5
	movdqa xmm9, xmm4
	movdqa xmm10, xmm15
	movdqa xmm11, xmm6
	movdqa xmm12, xmm14
	movdqa xmm14, xmm1
	movdqa xmm15, xmm2
	movdqa xmm1, xmm15
	psrlw xmm1, 4
	movdqa xmm0, xmm15
	psllw xmm0, 12
	pxor xmm1, xmm0
	movdqa xmm7, xmm1
	psrlq xmm7, 16
	psllq xmm1, 48
	pxor xmm7, xmm1
	pxor xmm15, xmm7
	pshufd xmm0, xmm15, 177
	movdqa xmm1, xmm0
	psrlw xmm0, 8
	psllw xmm1, 8
	pxor xmm0, xmm1
	pxor xmm7, xmm0
	movdqa xmm2, xmm8
	psrlw xmm2, 4
	movdqa xmm1, xmm8
	psllw xmm1, 12
	pxor xmm2, xmm1
	movdqa xmm0, xmm2
	psrlq xmm0, 16
	psllq xmm2, 48
	pxor xmm0, xmm2
	pxor xmm8, xmm0
	pshufd xmm1, xmm8, 177
	movdqa xmm2, xmm1
	psrlw xmm1, 8
	psllw xmm2, 8
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pxor xmm0, xmm15
	movdqa xmm3, xmm9
	psrlw xmm3, 4
	movdqa xmm2, xmm9
	psllw xmm2, 12
	pxor xmm3, xmm2
	movdqa xmm1, xmm3
	psrlq xmm1, 16
	psllq xmm3, 48
	pxor xmm1, xmm3
	pxor xmm9, xmm1
	pshufd xmm2, xmm9, 177
	movdqa xmm3, xmm2
	psrlw xmm2, 8
	psllw xmm3, 8
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pxor xmm1, xmm8
	pxor xmm1, xmm15
	movdqa xmm4, xmm10
	psrlw xmm4, 4
	movdqa xmm3, xmm10
	psllw xmm3, 12
	pxor xmm4, xmm3
	movdqa xmm2, xmm4
	psrlq xmm2, 16
	psllq xmm4, 48
	pxor xmm2, xmm4
	pxor xmm10, xmm2
	pshufd xmm3, xmm10, 177
	movdqa xmm4, xmm3
	psrlw xmm3, 8
	psllw xmm4, 8
	pxor xmm3, xmm4
	pxor xmm2, xmm3
	pxor xmm2, xmm9
	movdqa xmm5, xmm11
	psrlw xmm5, 4
	movdqa xmm4, xmm11
	psllw xmm4, 12
	pxor xmm5, xmm4
	movdqa xmm3, xmm5
	psrlq xmm3, 16
	psllq xmm5, 48
	pxor xmm3, xmm5
	pxor xmm11, xmm3
	pshufd xmm4, xmm11, 177
	movdqa xmm5, xmm4
	psrlw xmm4, 8
	psllw xmm5, 8
	pxor xmm4, xmm5
	pxor xmm3, xmm4
	pxor xmm3, xmm10
	pxor xmm3, xmm15
	movdqa xmm6, xmm12
	psrlw xmm6, 4
	movdqa xmm5, xmm12
	psllw xmm5, 12
	pxor xmm6, xmm5
	movdqa xmm4, xmm6
	psrlq xmm4, 16
	psllq xmm6, 48
	pxor xmm4, xmm6
	pxor xmm12, xmm4
	pshufd xmm5, xmm12, 177
	movdqa xmm6, xmm5
	psrlw xmm5, 8
	psllw xmm6, 8
	pxor xmm5, xmm6
	pxor xmm4, xmm5
	pxor xmm4, xmm11
	pxor xmm4, xmm15
	movdqa xmm8, xmm13
	psrlw xmm8, 4
	movdqa xmm6, xmm13
	psllw xmm6, 12
	pxor xmm8, xmm6
	movdqa xmm5, xmm8
	psrlq xmm5, 16
	psllq xmm8, 48
	pxor xmm5, xmm8
	pxor xmm13, xmm5
	pshufd xmm6, xmm13, 177
	movdqa xmm8, xmm6
	psrlw xmm6, 8
	psllw xmm8, 8
	pxor xmm6, xmm8
	pxor xmm5, xmm6
	pxor xmm5, xmm12
	movdqa xmm9, xmm14
	psrlw xmm9, 4
	movdqa xmm8, xmm14
	psllw xmm8, 12
	pxor xmm9, xmm8
	movdqa xmm6, xmm9
	psrlq xmm6, 16
	psllq xmm9, 48
	pxor xmm6, xmm9
	pxor xmm14, xmm6
	pshufd xmm8, xmm14, 177
	movdqa xmm9, xmm8
	psrlw xmm8, 8
	psllw xmm9, 8
	pxor xmm8, xmm9
	pxor xmm6, xmm8
	pxor xmm6, xmm13
	pxor xmm7, xmm14
	movdqu xmm8, XMMWORD PTR [rax]
	pshufd xmm9, xmm8, 68
	pshufd xmm8, xmm8, 238
	pxor xmm0, xmm9
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rax+16]
	pshufd xmm9, xmm8, 68
	pshufd xmm8, xmm8, 238
	pxor xmm2, xmm9
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rax+32]
	pshufd xmm9, xmm8, 68
	pshufd xmm8, xmm8, 238
	pxor xmm4, xmm9
	pxor xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rax+48]
	pshufd xmm9, xmm8, 68
	pshufd xmm8, xmm8, 238
	pxor xmm6, xmm9
	pxor xmm7, xmm8
	add rax, 64
	pxor xmm2, xmm5
	movdqa xmm8, xmm2
	pxor xmm8, xmm1
	movdqa xmm9, xmm8
	pxor xmm9, xmm6
	pxor xmm3, xmm9
	pxor xmm3, xmm7
	pxor xmm0, xmm8
	movdqa xmm10, xmm3
	pxor xmm10, xmm2
	movdqa xmm11, xmm10
	pxor xmm11, xmm0
	pxor xmm5, xmm11
	movdqa xmm12, xmm5
	pxor xmm12, xmm7
	movdqa xmm13, xmm11
	pxor xmm13, xmm9
	movdqa xmm14, xmm11
	pxor xmm14, xmm4
	movdqa xmm15, xmm14
	pand xmm15, xmm11
	movdqu XMMWORD PTR [r9], xmm11
	movdqa xmm11, xmm14
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r9+16], xmm5
	movdqa xmm5, xmm14
	pxor xmm5, xmm3
	pxor xmm3, xmm4
	movdqu XMMWORD PTR [r9+32], xmm14
	movdqa xmm14, xmm12
	pand xmm14, xmm9
	movdqu XMMWORD PTR [r9+48], xmm9
	movdqa xmm9, xmm11
	pand xmm9, xmm13
	movdqu XMMWORD PTR [r9+64], xmm11
	movdqa xmm11, xmm12
	pxor xmm11, xmm6
	pxor xmm4, xmm10
	movdqu XMMWORD PTR [r9+80], xmm12
	movdqa xmm12, xmm4
	pand xmm12, xmm5
	pxor xmm9, xmm12
	movdqu XMMWORD PTR [r9+96], xmm5
	movdqa xmm5, xmm7
	pand xmm5, xmm8
	pxor xmm12, xmm14
	pxor xmm5, xmm15
	pxor xmm5, xmm12
	movdqa xmm14, xmm0
	pxor xmm14, xmm7
	pxor xmm1, xmm4
	pxor xmm5, xmm11
	movdqa xmm11, xmm0
	pand xmm11, xmm3
	pxor xmm12, xmm11
	movdqu XMMWORD PTR [r9+112], xmm0
	movdqa xmm0, xmm14
	pand xmm0, xmm1
	pxor xmm0, xmm9
	pxor xmm0, xmm15
	pxor xmm0, xmm2
	movdqu xmm15, XMMWORD PTR [r9+16]
	movdqa xmm2, xmm15
	pand xmm2, xmm6
	movdqu XMMWORD PTR [r9+128], xmm6
	movdqa xmm6, xmm15
	pxor xmm6, xmm8
	pxor xmm12, xmm2
	pxor xmm12, xmm6
	movdqa xmm2, xmm4
	pxor xmm2, xmm15
	movdqa xmm6, xmm13
	pxor xmm6, xmm1
	movdqa xmm15, xmm2
	pand xmm15, xmm6
	pxor xmm9, xmm15
	pxor xmm9, xmm11
	movdqa xmm15, xmm5
	pand xmm15, xmm0
	pxor xmm9, xmm10
	movdqa xmm11, xmm12
	pxor xmm11, xmm15
	pxor xmm15, xmm9
	movdqa xmm10, xmm0
	pxor xmm10, xmm9
	pand xmm11, xmm10
	pxor xmm5, xmm12
	pxor xmm11, xmm9
	pxor xmm0, xmm11
	movdqa xmm10, xmm15
	pxor xmm10, xmm11
	pand xmm9, xmm10
	pxor xmm0, xmm9
	pand xmm8, xmm11
	pxor xmm9, xmm15
	pand xmm15, xmm5
	pxor xmm12, xmm15
	pand xmm9, xmm12
	pxor xmm9, xmm5
	movdqu xmm10, XMMWORD PTR [r9+64]
	pand xmm10, xmm9
	pand xmm7, xmm11
	movdqa xmm15, xmm12
	pxor xmm15, xmm9
	pand xmm6, xmm15
	pand xmm1, xmm12
	pand xmm14, xmm12
	pand xmm13, xmm9
	pxor xmm12, xmm11
	pxor xmm6, xmm13
	pand xmm15, xmm2
	pxor xmm13, xmm1
	pand xmm3, xmm12
	pxor xmm11, xmm0
	pxor xmm9, xmm0
	movdqu xmm5, XMMWORD PTR [r9+112]
	pand xmm5, xmm12
	movdqu xmm2, XMMWORD PTR [r9+48]
	pand xmm2, xmm0
	pxor xmm2, xmm8
	pxor xmm5, xmm15
	pxor xmm3, xmm6
	pxor xmm12, xmm9
	movdqu xmm1, XMMWORD PTR [r9+80]
	pand xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r9+96]
	pand xmm1, xmm12
	pxor xmm15, xmm7
	pand xmm12, xmm4
	pxor xmm6, xmm1
	movdqu xmm4, XMMWORD PTR [r9+32]
	pand xmm4, xmm9
	pxor xmm13, xmm2
	pxor xmm12, xmm10
	pxor xmm4, xmm12
	pxor xmm5, xmm12
	pxor xmm5, xmm13
	pxor xmm15, xmm4
	pxor xmm4, xmm14
	pxor xmm14, xmm5
	pxor xmm6, xmm8
	movdqu xmm12, XMMWORD PTR [r9+16]
	pand xmm12, xmm11
	pxor xmm1, xmm4
	pxor xmm14, xmm0
	pxor xmm13, xmm4
	movdqu xmm8, XMMWORD PTR [r9+128]
	pand xmm11, xmm8
	pxor xmm14, xmm10
	pxor xmm2, xmm1
	pxor xmm6, xmm11
	movdqu xmm0, XMMWORD PTR [r9]
	pand xmm9, xmm0
	pxor xmm2, xmm9
	pxor xmm14, xmm7
	pxor xmm15, xmm12
	pxor xmm1, xmm15
	pxor xmm6, xmm9
	pxor xmm1, xmm3
	movdqa xmm8, xmm5
	movdqa xmm9, xmm4
	movdqa xmm10, xmm15
	movdqa xmm11, xmm6
	movdqa xmm12, xmm14
	movdqa xmm14, xmm1
	movdqa xmm15, xmm2
	movdqu xmm1, XMMWORD PTR [r9+240]
	movdqa xmm0, xmm8
	psrlw xmm0, 8
	pxor xmm0, xmm8
	pand xmm0, xmm1
	pxor xmm8, xmm0
	psllw xmm0, 8
	pxor xmm8, xmm0
	movdqa xmm0, xmm9
	psrlw xmm0, 8
	pxor xmm0, xmm9
	pand xmm0, xmm1
	pxor xmm9, xmm0
	psllw xmm0, 8
	pxor xmm9, xmm0
	movdqa xmm0, xmm10
	psrlw xmm0, 8
	pxor xmm0, xmm10
	pand xmm0, xmm1
	pxor xmm10, xmm0
	psllw xmm0, 8
	pxor xmm10, xmm0
	movdqa xmm0, xmm11
	psrlw xmm0, 8
	pxor xmm0, xmm11
	pand xmm0, xmm1
	pxor xmm11, xmm0
	psllw xmm0, 8
	pxor xmm11, xmm0
	movdqa xmm0, xmm12
	psrlw xmm0, 8
	pxor xmm0, xmm12
	pand xmm0, xmm1
	pxor xmm12, xmm0
	psllw xmm0, 8
	pxor xmm12, xmm0
	movdqa xmm0, xmm13
	psrlw xmm0, 8
	pxor xmm0, xmm13
	pand xmm0, xmm1
	pxor xmm13, xmm0
	psllw xmm0, 8
	pxor xmm13, xmm0
	movdqa xmm0, xmm14
	psrlw xmm0, 8
	pxor xmm0, xmm14
	pand xmm0, xmm1
	pxor xmm14, xmm0
	psllw xmm0, 8
	pxor xmm14, xmm0
	movdqa xmm0, xmm15
	psrlw xmm0, 8
	pxor xmm0, xmm15
	pand xmm0, xmm1
	pxor xmm15, xmm0
	psllw xmm0, 8
	pxor xmm15, xmm0
	movdqa xmm7, xmm15
	psrlq xmm7, 16
	movdqa xmm0, xmm15
	psllq xmm0, 48
	pxor xmm7, xmm0
	pxor xmm15, xmm7
	pshufd xmm0, xmm15, 177
	pxor xmm7, xmm0
	movdqa xmm0, xmm8
	psrlq xmm0, 16
	movdqa xmm1, xmm8
	psllq xmm1, 48
	pxor xmm0, xmm1
	pxor xmm8, xmm0
	pshufd xmm1, xmm8, 177
	pxor xmm0, xmm1
	pxor xmm0, xmm15
	movdqa xmm1, xmm9
	psrlq xmm1, 16
	movdqa xmm2, xmm9
	psllq xmm2, 48
	pxor xmm1, xmm2
	pxor xmm9, xmm1
	pshufd xmm2, xmm9, 177
	pxor xmm1, xmm2
	pxor xmm1, xmm8
	pxor xmm1, xmm15
	movdqa xmm2, xmm10
	psrlq xmm2, 16
	movdqa xmm3, xmm10
	psllq xmm3, 48
	pxor xmm2, xmm3
	pxor xmm10, xmm2
	pshufd xmm3, xmm10, 177
	pxor xmm2, xmm3
	pxor xmm2, xmm9
	movdqa xmm3, xmm11
	psrlq xmm3, 16
	movdqa xmm4, xmm11
	psllq xmm4, 48
	pxor xmm3, xmm4
	pxor xmm11, xmm3
	pshufd xmm4, xmm11, 177
	pxor xmm3, xmm4
	pxor xmm3, xmm10
	pxor xmm3, xmm15
	movdqa xmm4, xmm12
	psrlq xmm4, 16
	movdqa xmm5, xmm12
	psllq xmm5, 48
	pxor xmm4, xmm5
	pxor xmm12, xmm4
	pshufd xmm5, xmm12, 177
	pxor xmm4, xmm5
	pxor xmm4, xmm11
	pxor xmm4, xmm15
	movdqa xmm5, xmm13
	psrlq xmm5, 16
	movdqa xmm6, xmm13
	psllq xmm6, 48
	pxor xmm5, xmm6
	pxor xmm13, xmm5
	pshufd xmm6, xmm13, 177
	pxor xmm5, xmm6
	pxor xmm5, xmm12
	movdqa xmm6, xmm14
	psrlq xmm6, 16
	movdqa xmm8, xmm14
	psllq xmm8, 48
	pxor xmm6, xmm8
	pxor xmm14, xmm6
	pshufd xmm8, xmm14, 177
	pxor xmm6, xmm8
	pxor xmm6, xmm13
	pxor xmm7, xmm14
	movdqu xmm8, XMMWORD PTR [rax]
	pshufd xmm9, xmm8, 68
	pshufd xmm8, xmm8, 238
	pxor xmm0, xmm9
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rax+16]
	pshufd xmm9, xmm8, 68
	pshufd xmm8, xmm8, 238
	pxor xmm2, xmm9
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rax+32]
	pshufd xmm9, xmm8, 68
	pshufd xmm8, xmm8, 238
	pxor xmm4, xmm9
	pxor xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rax+48]
	pshufd xmm9, xmm8, 68
	pshufd xmm8, xmm8, 238
	pxor xmm6, xmm9
	pxor xmm7, xmm8
	add rax, 64
	sub r10, 1
	jne 25b
	pxor xmm2, xmm5
	movdqa xmm8, xmm2
	pxor xmm8, xmm1
	movdqa xmm9, xmm8
	pxor xmm9, xmm6
	pxor xmm3, xmm9
	pxor xmm3, xmm7
	pxor xmm0, xmm8
	movdqa xmm10, xmm3
	pxor xmm10, xmm2
	movdqa xmm11, xmm10
	pxor xmm11, xmm0
	pxor xmm5, xmm11
	movdqa xmm12, xmm5
	pxor xmm12, xmm7
	movdqa xmm13, xmm11
	pxor xmm13, xmm9
	movdqa xmm14, xmm11
	pxor xmm14, xmm4
	movdqa xmm15, xmm14
	pand xmm15, xmm11
	movdqu XMMWORD PTR [r9], xmm11
	movdqa xmm11, xmm14
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r9+16], xmm5
	movdqa xmm5, xmm14
	pxor xmm5, xmm3
	pxor xmm3, xmm4
	movdqu XMMWORD PTR [r9+32], xmm14
	movdqa xmm14, xmm12
	pand xmm14, xmm9
	movdqu XMMWORD PTR [r9+48], xmm9
	movdqa xmm9, xmm11
	pand xmm9, xmm13
	movdqu XMMWORD PTR [r9+64], xmm11
	movdqa xmm11, xmm12
	pxor xmm11, xmm6
	pxor xmm4, xmm10
	movdqu XMMWORD PTR [r9+80], xmm12
	movdqa xmm12, xmm4
	pand xmm12, xmm5
	pxor xmm9, xmm12
	movdqu XMMWORD PTR [r9+96], xmm5
	movdqa xmm5, xmm7
	pand xmm5, xmm8
	pxor xmm12, xmm14
	pxor xmm5, xmm15
	pxor xmm5, xmm12
	movdqa xmm14, xmm0
	pxor xmm14, xmm7
	pxor xmm1, xmm4
	pxor xmm5, xmm11
	movdqa xmm11, xmm0
	pand xmm11, xmm3
	pxor xmm12, xmm11
	movdqu XMMWORD PTR [r9+112], xmm0
	movdqa xmm0, xmm14
	pand xmm0, xmm1
	pxor xmm0, xmm9
	pxor xmm0, xmm15
	pxor xmm0, xmm2
	movdqu xmm15, XMMWORD PTR [r9+16]
	movdqa xmm2, xmm15
	pand xmm2, xmm6
	movdqu XMMWORD PTR [r9+128], xmm6
	movdqa xmm6, xmm15
	pxor xmm6, xmm8
	pxor xmm12, xmm2
	pxor xmm12, xmm6
	movdqa xmm2, xmm4
	pxor xmm2, xmm15
	movdqa xmm6, xmm13
	pxor xmm6, xmm1
	movdqa xmm15, xmm2
	pand xmm15, xmm6
	pxor xmm9, xmm15
	pxor xmm9, xmm11
	movdqa xmm15, xmm5
	pand xmm15, xmm0
	pxor xmm9, xmm10
	movdqa xmm11, xmm12
	pxor xmm11, xmm15
	pxor xmm15, xmm9
	movdqa xmm10, xmm0
	pxor xmm10, xmm9
	pand xmm11, xmm10
	pxor xmm5, xmm12
	pxor xmm11, xmm9
	pxor xmm0, xmm11
	movdqa xmm10, xmm15
	pxor xmm10, xmm11
	pand xmm9, xmm10
	pxor xmm0, xmm9
	pand xmm8, xmm11
	pxor xmm9, xmm15
	pand xmm15, xmm5
	pxor xmm12, xmm15
	pand xmm9, xmm12
	pxor xmm9, xmm5
	movdqu xmm10, XMMWORD PTR [r9+64]
	pand xmm10, xmm9
	pand xmm7, xmm11
	movdqa xmm15, xmm12
	pxor xmm15, xmm9
	pand xmm6, xmm15
	pand xmm1, xmm12
	pand xmm14, xmm12
	pand xmm13, xmm9
	pxor xmm12, xmm11
	pxor xmm6, xmm13
	pand xmm15, xmm2
	pxor xmm13, xmm1
	pand xmm3, xmm12
	pxor xmm11, xmm0
	pxor xmm9, xmm0
	movdqu xmm5, XMMWORD PTR [r9+112]
	pand xmm5, xmm12
	movdqu xmm2, XMMWORD PTR [r9+48]
	pand xmm2, xmm0
	pxor xmm2, xmm8
	pxor xmm5, xmm15
	pxor xmm3, xmm6
	pxor xmm12, xmm9
	movdqu xmm1, XMMWORD PTR [r9+80]
	pand xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r9+96]
	pand xmm1, xmm12
	pxor xmm15, xmm7
	pand xmm12, xmm4
	pxor xmm6, xmm1
	movdqu xmm4, XMMWORD PTR [r9+32]
	pand xmm4, xmm9
	pxor xmm13, xmm2
	pxor xmm12, xmm10
	pxor xmm4, xmm12
	pxor xmm5, xmm12
	pxor xmm5, xmm13
	pxor xmm15, xmm4
	pxor xmm4, xmm14
	pxor xmm14, xmm5
	pxor xmm6, xmm8
	movdqu xmm12, XMMWORD PTR [r9+16]
	pand xmm12, xmm11
	pxor xmm1, xmm4
	pxor xmm14, xmm0
	pxor xmm13, xmm4
	movdqu xmm8, XMMWORD PTR [r9+128]
	pand xmm11, xmm8
	pxor xmm14, xmm10
	pxor xmm2, xmm1
	pxor xmm6, xmm11
	movdqu xmm0, XMMWORD PTR [r9]
	pand xmm9, xmm0
	pxor xmm2, xmm9
	pxor xmm14, xmm7
	pxor xmm15, xmm12
	pxor xmm1, xmm15
	pxor xmm6, xmm9
	pxor xmm1, xmm3
	movdqa xmm8, xmm5
	movdqa xmm9, xmm4
	movdqa xmm10, xmm15
	movdqa xmm11, xmm6
	movdqa xmm12, xmm14
	movdqa xmm14, xmm1
	movdqa xmm15, xmm2
	movdqa xmm1, xmm15
	psrlw xmm1, 4
	movdqa xmm0, xmm15
	psllw xmm0, 12
	pxor xmm1, xmm0
	movdqa xmm7, xmm1
	psrlq xmm7, 16
	psllq xmm1, 48
	pxor xmm7, xmm1
	pxor xmm15, xmm7
	pshufd xmm0, xmm15, 177
	movdqa xmm1, xmm0
	psrlw xmm0, 8
	psllw xmm1, 8
	pxor xmm0, xmm1
	pxor xmm7, xmm0
	movdqa xmm2, xmm8
	psrlw xmm2, 4
	movdqa xmm1, xmm8
	psllw xmm1, 12
	pxor xmm2, xmm1
	movdqa xmm0, xmm2
	psrlq xmm0, 16
	psllq xmm2, 48
	pxor xmm0, xmm2
	pxor xmm8, xmm0
	pshufd xmm1, xmm8, 177
	movdqa xmm2, xmm1
	psrlw xmm1, 8
	psllw xmm2, 8
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pxor xmm0, xmm15
	movdqa xmm3, xmm9
	psrlw xmm3, 4
	movdqa xmm2, xmm9
	psllw xmm2, 12
	pxor xmm3, xmm2
	movdqa xmm1, xmm3
	psrlq xmm1, 16
	psllq xmm3, 48
	pxor xmm1, xmm3
	pxor xmm9, xmm1
	pshufd xmm2, xmm9, 177
	movdqa xmm3, xmm2
	psrlw xmm2, 8
	psllw xmm3, 8
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pxor xmm1, xmm8
	pxor xmm1, xmm15
	movdqa xmm4, xmm10
	psrlw xmm4, 4
	movdqa xmm3, xmm10
	psllw xmm3, 12
	pxor xmm4, xmm3
	movdqa xmm2, xmm4
	psrlq xmm2, 16
	psllq xmm4, 48
	pxor xmm2, xmm4
	pxor xmm10, xmm2
	pshufd xmm3, xmm10, 177
	movdqa xmm4, xmm3
	psrlw xmm3, 8
	psllw xmm4, 8
	pxor xmm3, xmm4
	pxor xmm2, xmm3
	pxor xmm2, xmm9
	movdqa xmm5, xmm11
	psrlw xmm5, 4
	movdqa xmm4, xmm11
	psllw xmm4, 12
	pxor xmm5, xmm4
	movdqa xmm3, xmm5
	psrlq xmm3, 16
	psllq xmm5, 48
	pxor xmm3, xmm5
	pxor xmm11, xmm3
	pshufd xmm4, xmm11, 177
	movdqa xmm5, xmm4
	psrlw xmm4, 8
	psllw xmm5, 8
	pxor xmm4, xmm5
	pxor xmm3, xmm4
	pxor xmm3, xmm10
	pxor xmm3, xmm15
	movdqa xmm6, xmm12
	psrlw xmm6, 4
	movdqa xmm5, xmm12
	psllw xmm5, 12
	pxor xmm6, xmm5
	movdqa xmm4, xmm6
	psrlq xmm4, 16
	psllq xmm6, 48
	pxor xmm4, xmm6
	pxor xmm12, xmm4
	pshufd xmm5, xmm12, 177
	movdqa xmm6, xmm5
	psrlw xmm5, 8
	psllw xmm6, 8
	pxor xmm5, xmm6
	pxor xmm4, xmm5
	pxor xmm4, xmm11
	pxor xmm4, xmm15
	movdqa xmm8, xmm13
	psrlw xmm8, 4
	movdqa xmm6, xmm13
	psllw xmm6, 12
	pxor xmm8, xmm6
	movdqa xmm5, xmm8
	psrlq xmm5, 16
	psllq xmm8, 48
	pxor xmm5, xmm8
	pxor xmm13, xmm5
	pshufd xmm6, xmm13, 177
	movdqa xmm8, xmm6
	psrlw xmm6, 8
	psllw xmm8, 8
	pxor xmm6, xmm8
	pxor xmm5, xmm6
	pxor xmm5, xmm12
	movdqa xmm9, xmm14
	psrlw xmm9, 4
	movdqa xmm8, xmm14
	psllw xmm8, 12
	pxor xmm9, xmm8
	movdqa xmm6, xmm9
	psrlq xmm6, 16
	psllq xmm9, 48
	pxor xmm6, xmm9
	pxor xmm14, xmm6
	pshufd xmm8, xmm14, 177
	movdqa xmm9, xmm8
	psrlw xmm8, 8
	psllw xmm9, 8
	pxor xmm8, xmm9
	pxor xmm6, xmm8
	pxor xmm6, xmm13
	pxor xmm7, xmm14
	movdqu xmm8, XMMWORD PTR [rax]
	pshufd xmm9, xmm8, 68
	pshufd xmm8, xmm8, 238
	pxor xmm0, xmm9
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rax+16]
	pshufd xmm9, xmm8, 68
	pshufd xmm8, xmm8, 238
	pxor xmm2, xmm9
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rax+32]
	pshufd xmm9, xmm8, 68
	pshufd xmm8, xmm8, 238
	pxor xmm4, xmm9
	pxor xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rax+48]
	pshufd xmm9, xmm8, 68
	pshufd xmm8, xmm8, 238
	pxor xmm6, xmm9
	pxor xmm7, xmm8
	add rax, 64
	pxor xmm2, xmm5
	movdqa xmm8, xmm2
	pxor xmm8, xmm1
	movdqa xmm9, xmm8
	pxor xmm9, xmm6
	pxor xmm3, xmm9
	pxor xmm3, xmm7
	pxor xmm0, xmm8
	movdqa xmm10, xmm3
	pxor xmm10, xmm2
	movdqa xmm11, xmm10
	pxor xmm11, xmm0
	pxor xmm5, xmm11
	movdqa xmm12, xmm5
	pxor xmm12, xmm7
	movdqa xmm13, xmm11
	pxor xmm13, xmm9
	movdqa xmm14, xmm11
	pxor xmm14, xmm4
	movdqa xmm15, xmm14
	pand xmm15, xmm11
	movdqu XMMWORD PTR [r9], xmm11
	movdqa xmm11, xmm14
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r9+16], xmm5
	movdqa xmm5, xmm14
	pxor xmm5, xmm3
	pxor xmm3, xmm4
	movdqu XMMWORD PTR [r9+32], xmm14
	movdqa xmm14, xmm12
	pand xmm14, xmm9
	movdqu XMMWORD PTR [r9+48], xmm9
	movdqa xmm9, xmm11
	pand xmm9, xmm13
	movdqu XMMWORD PTR [r9+64], xmm11
	movdqa xmm11, xmm12
	pxor xmm11, xmm6
	pxor xmm4, xmm10
	movdqu XMMWORD PTR [r9+80], xmm12
	movdqa xmm12, xmm4
	pand xmm12, xmm5
	pxor xmm9, xmm12
	movdqu XMMWORD PTR [r9+96], xmm5
	movdqa xmm5, xmm7
	pand xmm5, xmm8
	pxor xmm12, xmm14
	pxor xmm5, xmm15
	pxor xmm5, xmm12
	movdqa xmm14, xmm0
	pxor xmm14, xmm7
	pxor xmm1, xmm4
	pxor xmm5, xmm11
	movdqa xmm11, xmm0
	pand xmm11, xmm3
	pxor xmm12, xmm11
	movdqu XMMWORD PTR [r9+112], xmm0
	movdqa xmm0, xmm14
	pand xmm0, xmm1
	pxor xmm0, xmm9
	pxor xmm0, xmm15
	pxor xmm0, xmm2
	movdqu xmm15, XMMWORD PTR [r9+16]
	movdqa xmm2, xmm15
	pand xmm2, xmm6
	movdqu XMMWORD PTR [r9+128], xmm6
	movdqa xmm6, xmm15
	pxor xmm6, xmm8
	pxor xmm12, xmm2
	pxor xmm12, xmm6
	movdqa xmm2, xmm4
	pxor xmm2, xmm15
	movdqa xmm6, xmm13
	pxor xmm6, xmm1
	movdqa xmm15, xmm2
	pand xmm15, xmm6
	pxor xmm9, xmm15
	pxor xmm9, xmm11
	movdqa xmm15, xmm5
	pand xmm15, xmm0
	pxor xmm9, xmm10
	movdqa xmm11, xmm12
	pxor xmm11, xmm15
	pxor xmm15, xmm9
	movdqa xmm10, xmm0
	pxor xmm10, xmm9
	pand xmm11, xmm10
	pxor xmm5, xmm12
	pxor xmm11, xmm9
	pxor xmm0, xmm11
	movdqa xmm10, xmm15
	pxor xmm10, xmm11
	pand xmm9, xmm10
	pxor xmm0, xmm9
	pand xmm8, xmm11
	pxor xmm9, xmm15
	pand xmm15, xmm5
	pxor xmm12, xmm15
	pand xmm9, xmm12
	pxor xmm9, xmm5
	movdqu xmm10, XMMWORD PTR [r9+64]
	pand xmm10, xmm9
	pand xmm7, xmm11
	movdqa xmm15, xmm12
	pxor xmm15, xmm9
	pand xmm6, xmm15
	pand xmm1, xmm12
	pand xmm14, xmm12
	pand xmm13, xmm9
	pxor xmm12, xmm11
	pxor xmm6, xmm13
	pand xmm15, xmm2
	pxor xmm13, xmm1
	pand xmm3, xmm12
	pxor xmm11, xmm0
	pxor xmm9, xmm0
	movdqu xmm5, XMMWORD PTR [r9+112]
	pand xmm5, xmm12
	movdqu xmm2, XMMWORD PTR [r9+48]
	pand xmm2, xmm0
	pxor xmm2, xmm8
	pxor xmm5, xmm15
	pxor xmm3, xmm6
	pxor xmm12, xmm9
	movdqu xmm1, XMMWORD PTR [r9+80]
	pand xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r9+96]
	pand xmm1, xmm12
	pxor xmm15, xmm7
	pand xmm12, xmm4
	pxor xmm6, xmm1
	movdqu xmm4, XMMWORD PTR [r9+32]
	pand xmm4, xmm9
	pxor xmm13, xmm2
	pxor xmm12, xmm10
	pxor xmm4, xmm12
	pxor xmm5, xmm12
	pxor xmm5, xmm13
	pxor xmm15, xmm4
	pxor xmm4, xmm14
	pxor xmm14, xmm5
	pxor xmm6, xmm8
	movdqu xmm12, XMMWORD PTR [r9+16]
	pand xmm12, xmm11
	pxor xmm1, xmm4
	pxor xmm14, xmm0
	pxor xmm13, xmm4
	movdqu xmm8, XMMWORD PTR [r9+128]
	pand xmm11, xmm8
	pxor xmm14, xmm10
	pxor xmm2, xmm1
	pxor xmm6, xmm11
	movdqu xmm0, XMMWORD PTR [r9]
	pand xmm9, xmm0
	pxor xmm2, xmm9
	pxor xmm14, xmm7
	pxor xmm15, xmm12
	pxor xmm1, xmm15
	pxor xmm6, xmm9
	pxor xmm1, xmm3
	movdqa xmm8, xmm5
	movdqa xmm9, xmm4
	movdqa xmm10, xmm15
	movdqa xmm11, xmm6
	movdqa xmm12, xmm14
	movdqa xmm14, xmm1
	movdqa xmm15, xmm2
	movdqu xmm1, XMMWORD PTR [r9+240]
	movdqa xmm0, xmm8
	psrlw xmm0, 8
	pxor xmm0, xmm8
	pand xmm0, xmm1
	pxor xmm8, xmm0
	psllw xmm0, 8
	pxor xmm8, xmm0
	movdqa xmm0, xmm9
	psrlw xmm0, 8
	pxor xmm0, xmm9
	pand xmm0, xmm1
	pxor xmm9, xmm0
	psllw xmm0, 8
	pxor xmm9, xmm0
	movdqa xmm0, xmm10
	psrlw xmm0, 8
	pxor xmm0, xmm10
	pand xmm0, xmm1
	pxor xmm10, xmm0
	psllw xmm0, 8
	pxor xmm10, xmm0
	movdqa xmm0, xmm11
	psrlw xmm0, 8
	pxor xmm0, xmm11
	pand xmm0, xmm1
	pxor xmm11, xmm0
	psllw xmm0, 8
	pxor xmm11, xmm0
	movdqa xmm0, xmm12
	psrlw xmm0, 8
	pxor xmm0, xmm12
	pand xmm0, xmm1
	pxor xmm12, xmm0
	psllw xmm0, 8
	pxor xmm12, xmm0
	movdqa xmm0, xmm13
	psrlw xmm0, 8
	pxor xmm0, xmm13
	pand xmm0, xmm1
	pxor xmm13, xmm0
	psllw xmm0, 8
	pxor xmm13, xmm0
	movdqa xmm0, xmm14
	psrlw xmm0, 8
	pxor xmm0, xmm14
	pand xmm0, xmm1
	pxor xmm14, xmm0
	psllw xmm0, 8
	pxor xmm14, xmm0
	movdqa xmm0, xmm15
	psrlw xmm0, 8
	pxor xmm0, xmm15
	pand xmm0, xmm1
	pxor xmm15, xmm0
	psllw xmm0, 8
	pxor xmm15, xmm0
	movdqu xmm0, XMMWORD PTR [rax]
	pshufd xmm1, xmm0, 68
	pshufd xmm0, xmm0, 238
	pxor xmm8, xmm1
	pxor xmm9, xmm0
	movdqu xmm0, XMMWORD PTR [rax+16]
	pshufd xmm1, xmm0, 68
	pshufd xmm0, xmm0, 238
	pxor xmm10, xmm1
	pxor xmm11, xmm0
	movdqu xmm0, XMMWORD PTR [rax+32]
	pshufd xmm1, xmm0, 68
	pshufd xmm0, xmm0, 238
	pxor xmm12, xmm1
	pxor xmm13, xmm0
	movdqu xmm0, XMMWORD PTR [rax+48]
	pshufd xmm1, xmm0, 68
	pshufd xmm0, xmm0, 238
	pxor xmm14, xmm1
	pxor xmm15, xmm0
	movdqa xmm0, xmm8
	movdqa xmm1, xmm9
	movdqa xmm2, xmm10
	movdqa xmm3, xmm11
	movdqa xmm4, xmm12
	movdqa xmm5, xmm13
	movdqa xmm6, xmm14
	movdqa xmm7, xmm15
	movdqu xmm9, XMMWORD PTR [r9+144]
	movdqa xmm8, xmm0
	psrlq xmm8, 1
	pxor xmm8, xmm1
	pand xmm8, xmm9
	pxor xmm1, xmm8
	psllq xmm8, 1
	pxor xmm0, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 1
	pxor xmm8, xmm3
	pand xmm8, xmm9
	pxor xmm3, xmm8
	psllq xmm8, 1
	pxor xmm2, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 1
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 1
	pxor xmm4, xmm8
	movdqa xmm8, xmm6
	psrlq xmm8, 1
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 1
	pxor xmm6, xmm8
	movdqu xmm9, XMMWORD PTR [r9+160]
	movdqa xmm8, xmm0
	psrlq xmm8, 2
	pxor xmm8, xmm2
	pand xmm8, xmm9
	pxor xmm2, xmm8
	psllq xmm8, 2
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 2
	pxor xmm8, xmm3
	pand xmm8, xmm9
	pxor xmm3, xmm8
	psllq xmm8, 2
	pxor xmm1, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 2
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 2
	pxor xmm4, xmm8
	movdqa xmm8, xmm5
	psrlq xmm8, 2
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 2
	pxor xmm5, xmm8
	movdqu xmm9, XMMWORD PTR [r9+176]
	movdqa xmm8, xmm0
	psrlq xmm8, 4
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 4
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 4
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 4
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 4
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 4
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 4
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 4
	pxor xmm3, xmm8
	movdqu xmm9, XMMWORD PTR [r9+224]
	movdqa xmm8, xmm0
	psrlq xmm8, 32
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 32
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 32
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 32
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 32
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 32
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 32
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 32
	pxor xmm3, xmm8
	movdqu xmm9, XMMWORD PTR [r9+208]
	movdqa xmm8, xmm0
	psrlq xmm8, 16
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 16
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 16
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 16
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 16
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 16
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 16
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 16
	pxor xmm3, xmm8
	movdqu xmm9, XMMWORD PTR [r9+192]
	movdqa xmm8, xmm0
	psrlq xmm8, 8
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 8
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 8
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 8
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 8
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 8
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 8
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 8
	pxor xmm3, xmm8
	movdqa xmm8, xmm0
	punpcklqdq xmm8, xmm4
	punpckhqdq xmm0, xmm4
	movdqu XMMWORD PTR [r9+288], xmm8
	movdqu XMMWORD PTR [r9+352], xmm0
	movdqa xmm8, xmm1
	punpcklqdq xmm8, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [r9+304], xmm8
	movdqu XMMWORD PTR [r9+368], xmm1
	movdqa xmm8, xmm2
	punpcklqdq xmm8, xmm6
	punpckhqdq xmm2, xmm6
	movdqu XMMWORD PTR [r9+320], xmm8
	movdqu XMMWORD PTR [r9+384], xmm2
	movdqa xmm8, xmm3
	punpcklqdq xmm8, xmm7
	punpckhqdq xmm3, xmm7
	movdqu XMMWORD PTR [r9+336], xmm8
	movdqu XMMWORD PTR [r9+400], xmm3
	mov rdi, 8
	cmp r8, 8
	cmovb rdi, r8
	mov r10, rdi
	mov rax, r9
	add rax, 288
26:
	movdqu xmm0, XMMWORD PTR [rax]
	movdqu xmm1, XMMWORD PTR [rcx]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r11], xmm0
	add rax, 16
	add rcx, 16
	add r11, 16
	sub r10, 1
	jne 26b
	mov eax, DWORD PTR [rdx+12]
	bswap eax
	add eax, edi
	bswap eax
	mov DWORD PTR [rdx+12], eax
	sub r8, rdi
	jne 24b
	jmp 21f
20:
21:
	ret
	.p2align 6
