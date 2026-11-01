// The functions of `src/sha256.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha224_init:
	movabs rax, 3926247204440088280
	movq xmm0, rax
	movabs rax, -644479594506691305
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	movabs rax, 7518782744944446257
	movq xmm0, rax
	movabs rax, -4685344894838272089
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi+16], xmm0
	ret
	.p2align 6

vg_sha256_compress:
	mov QWORD PTR [rcx+64], rbx
	mov QWORD PTR [rcx+72], rbp
	mov QWORD PTR [rcx+80], r12
	mov QWORD PTR [rcx+88], r13
	mov QWORD PTR [rcx+96], r14
	mov QWORD PTR [rcx+104], r15
	test rdx, rdx
	je 20f
22:
	mov eax, DWORD PTR [rdi]
	mov ebx, DWORD PTR [rdi+4]
	mov ebp, DWORD PTR [rdi+8]
	mov r8d, DWORD PTR [rdi+12]
	mov r9d, DWORD PTR [rdi+16]
	mov r10d, DWORD PTR [rdi+20]
	mov r11d, DWORD PTR [rdi+24]
	mov r12d, DWORD PTR [rdi+28]
	mov r13d, DWORD PTR [rsi]
	bswap r13d
	mov DWORD PTR [rcx], r13d
	mov r14d, r9d
	ror r14d, 6
	mov r15d, r9d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r12d, r14d
	mov r14d, r10d
	xor r14d, r11d
	and r14d, r9d
	xor r14d, r11d
	add r12d, r14d
	add r12d, 1116352408
	add r12d, r13d
	add r8d, r12d
	mov r14d, eax
	ror r14d, 2
	mov r15d, eax
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	or r14d, ebx
	and r14d, ebp
	mov r15d, eax
	and r15d, ebx
	or r14d, r15d
	add r12d, r14d
	mov r13d, DWORD PTR [rsi+4]
	bswap r13d
	mov DWORD PTR [rcx+4], r13d
	mov r14d, r8d
	ror r14d, 6
	mov r15d, r8d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r11d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r14d, r8d
	xor r14d, r10d
	add r11d, r14d
	add r11d, 1899447441
	add r11d, r13d
	add ebp, r11d
	mov r14d, r12d
	ror r14d, 2
	mov r15d, r12d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r11d, r14d
	mov r14d, r12d
	or r14d, eax
	and r14d, ebx
	mov r15d, r12d
	and r15d, eax
	or r14d, r15d
	add r11d, r14d
	mov r13d, DWORD PTR [rsi+8]
	bswap r13d
	mov DWORD PTR [rcx+8], r13d
	mov r14d, ebp
	ror r14d, 6
	mov r15d, ebp
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r8d
	xor r14d, r9d
	and r14d, ebp
	xor r14d, r9d
	add r10d, r14d
	add r10d, -1245643825
	add r10d, r13d
	add ebx, r10d
	mov r14d, r11d
	ror r14d, 2
	mov r15d, r11d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	or r14d, r12d
	and r14d, eax
	mov r15d, r11d
	and r15d, r12d
	or r14d, r15d
	add r10d, r14d
	mov r13d, DWORD PTR [rsi+12]
	bswap r13d
	mov DWORD PTR [rcx+12], r13d
	mov r14d, ebx
	ror r14d, 6
	mov r15d, ebx
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r9d, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r14d, ebx
	xor r14d, r8d
	add r9d, r14d
	add r9d, -373957723
	add r9d, r13d
	add eax, r9d
	mov r14d, r10d
	ror r14d, 2
	mov r15d, r10d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r9d, r14d
	mov r14d, r10d
	or r14d, r11d
	and r14d, r12d
	mov r15d, r10d
	and r15d, r11d
	or r14d, r15d
	add r9d, r14d
	mov r13d, DWORD PTR [rsi+16]
	bswap r13d
	mov DWORD PTR [rcx+16], r13d
	mov r14d, eax
	ror r14d, 6
	mov r15d, eax
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r8d, r14d
	mov r14d, ebx
	xor r14d, ebp
	and r14d, eax
	xor r14d, ebp
	add r8d, r14d
	add r8d, 961987163
	add r8d, r13d
	add r12d, r8d
	mov r14d, r9d
	ror r14d, 2
	mov r15d, r9d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	or r14d, r10d
	and r14d, r11d
	mov r15d, r9d
	and r15d, r10d
	or r14d, r15d
	add r8d, r14d
	mov r13d, DWORD PTR [rsi+20]
	bswap r13d
	mov DWORD PTR [rcx+20], r13d
	mov r14d, r12d
	ror r14d, 6
	mov r15d, r12d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add ebp, r14d
	mov r14d, eax
	xor r14d, ebx
	and r14d, r12d
	xor r14d, ebx
	add ebp, r14d
	add ebp, 1508970993
	add ebp, r13d
	add r11d, ebp
	mov r14d, r8d
	ror r14d, 2
	mov r15d, r8d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add ebp, r14d
	mov r14d, r8d
	or r14d, r9d
	and r14d, r10d
	mov r15d, r8d
	and r15d, r9d
	or r14d, r15d
	add ebp, r14d
	mov r13d, DWORD PTR [rsi+24]
	bswap r13d
	mov DWORD PTR [rcx+24], r13d
	mov r14d, r11d
	ror r14d, 6
	mov r15d, r11d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add ebx, r14d
	mov r14d, r12d
	xor r14d, eax
	and r14d, r11d
	xor r14d, eax
	add ebx, r14d
	add ebx, -1841331548
	add ebx, r13d
	add r10d, ebx
	mov r14d, ebp
	ror r14d, 2
	mov r15d, ebp
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	or r14d, r8d
	and r14d, r9d
	mov r15d, ebp
	and r15d, r8d
	or r14d, r15d
	add ebx, r14d
	mov r13d, DWORD PTR [rsi+28]
	bswap r13d
	mov DWORD PTR [rcx+28], r13d
	mov r14d, r10d
	ror r14d, 6
	mov r15d, r10d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add eax, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r14d, r10d
	xor r14d, r12d
	add eax, r14d
	add eax, -1424204075
	add eax, r13d
	add r9d, eax
	mov r14d, ebx
	ror r14d, 2
	mov r15d, ebx
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add eax, r14d
	mov r14d, ebx
	or r14d, ebp
	and r14d, r8d
	mov r15d, ebx
	and r15d, ebp
	or r14d, r15d
	add eax, r14d
	mov r13d, DWORD PTR [rsi+32]
	bswap r13d
	mov DWORD PTR [rcx+32], r13d
	mov r14d, r9d
	ror r14d, 6
	mov r15d, r9d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r12d, r14d
	mov r14d, r10d
	xor r14d, r11d
	and r14d, r9d
	xor r14d, r11d
	add r12d, r14d
	add r12d, -670586216
	add r12d, r13d
	add r8d, r12d
	mov r14d, eax
	ror r14d, 2
	mov r15d, eax
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	or r14d, ebx
	and r14d, ebp
	mov r15d, eax
	and r15d, ebx
	or r14d, r15d
	add r12d, r14d
	mov r13d, DWORD PTR [rsi+36]
	bswap r13d
	mov DWORD PTR [rcx+36], r13d
	mov r14d, r8d
	ror r14d, 6
	mov r15d, r8d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r11d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r14d, r8d
	xor r14d, r10d
	add r11d, r14d
	add r11d, 310598401
	add r11d, r13d
	add ebp, r11d
	mov r14d, r12d
	ror r14d, 2
	mov r15d, r12d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r11d, r14d
	mov r14d, r12d
	or r14d, eax
	and r14d, ebx
	mov r15d, r12d
	and r15d, eax
	or r14d, r15d
	add r11d, r14d
	mov r13d, DWORD PTR [rsi+40]
	bswap r13d
	mov DWORD PTR [rcx+40], r13d
	mov r14d, ebp
	ror r14d, 6
	mov r15d, ebp
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r8d
	xor r14d, r9d
	and r14d, ebp
	xor r14d, r9d
	add r10d, r14d
	add r10d, 607225278
	add r10d, r13d
	add ebx, r10d
	mov r14d, r11d
	ror r14d, 2
	mov r15d, r11d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	or r14d, r12d
	and r14d, eax
	mov r15d, r11d
	and r15d, r12d
	or r14d, r15d
	add r10d, r14d
	mov r13d, DWORD PTR [rsi+44]
	bswap r13d
	mov DWORD PTR [rcx+44], r13d
	mov r14d, ebx
	ror r14d, 6
	mov r15d, ebx
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r9d, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r14d, ebx
	xor r14d, r8d
	add r9d, r14d
	add r9d, 1426881987
	add r9d, r13d
	add eax, r9d
	mov r14d, r10d
	ror r14d, 2
	mov r15d, r10d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r9d, r14d
	mov r14d, r10d
	or r14d, r11d
	and r14d, r12d
	mov r15d, r10d
	and r15d, r11d
	or r14d, r15d
	add r9d, r14d
	mov r13d, DWORD PTR [rsi+48]
	bswap r13d
	mov DWORD PTR [rcx+48], r13d
	mov r14d, eax
	ror r14d, 6
	mov r15d, eax
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r8d, r14d
	mov r14d, ebx
	xor r14d, ebp
	and r14d, eax
	xor r14d, ebp
	add r8d, r14d
	add r8d, 1925078388
	add r8d, r13d
	add r12d, r8d
	mov r14d, r9d
	ror r14d, 2
	mov r15d, r9d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	or r14d, r10d
	and r14d, r11d
	mov r15d, r9d
	and r15d, r10d
	or r14d, r15d
	add r8d, r14d
	mov r13d, DWORD PTR [rsi+52]
	bswap r13d
	mov DWORD PTR [rcx+52], r13d
	mov r14d, r12d
	ror r14d, 6
	mov r15d, r12d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add ebp, r14d
	mov r14d, eax
	xor r14d, ebx
	and r14d, r12d
	xor r14d, ebx
	add ebp, r14d
	add ebp, -2132889090
	add ebp, r13d
	add r11d, ebp
	mov r14d, r8d
	ror r14d, 2
	mov r15d, r8d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add ebp, r14d
	mov r14d, r8d
	or r14d, r9d
	and r14d, r10d
	mov r15d, r8d
	and r15d, r9d
	or r14d, r15d
	add ebp, r14d
	mov r13d, DWORD PTR [rsi+56]
	bswap r13d
	mov DWORD PTR [rcx+56], r13d
	mov r14d, r11d
	ror r14d, 6
	mov r15d, r11d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add ebx, r14d
	mov r14d, r12d
	xor r14d, eax
	and r14d, r11d
	xor r14d, eax
	add ebx, r14d
	add ebx, -1680079193
	add ebx, r13d
	add r10d, ebx
	mov r14d, ebp
	ror r14d, 2
	mov r15d, ebp
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	or r14d, r8d
	and r14d, r9d
	mov r15d, ebp
	and r15d, r8d
	or r14d, r15d
	add ebx, r14d
	mov r13d, DWORD PTR [rsi+60]
	bswap r13d
	mov DWORD PTR [rcx+60], r13d
	mov r14d, r10d
	ror r14d, 6
	mov r15d, r10d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add eax, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r14d, r10d
	xor r14d, r12d
	add eax, r14d
	add eax, -1046744716
	add eax, r13d
	add r9d, eax
	mov r14d, ebx
	ror r14d, 2
	mov r15d, ebx
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add eax, r14d
	mov r14d, ebx
	or r14d, ebp
	and r14d, r8d
	mov r15d, ebx
	and r15d, ebp
	or r14d, r15d
	add eax, r14d
	mov r14d, DWORD PTR [rcx+56]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+36]
	mov r14d, DWORD PTR [rcx+4]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx]
	mov DWORD PTR [rcx], r13d
	mov r14d, r9d
	ror r14d, 6
	mov r15d, r9d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r12d, r14d
	mov r14d, r10d
	xor r14d, r11d
	and r14d, r9d
	xor r14d, r11d
	add r12d, r14d
	add r12d, -459576895
	add r12d, r13d
	add r8d, r12d
	mov r14d, eax
	ror r14d, 2
	mov r15d, eax
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	or r14d, ebx
	and r14d, ebp
	mov r15d, eax
	and r15d, ebx
	or r14d, r15d
	add r12d, r14d
	mov r14d, DWORD PTR [rcx+60]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+40]
	mov r14d, DWORD PTR [rcx+8]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+4]
	mov DWORD PTR [rcx+4], r13d
	mov r14d, r8d
	ror r14d, 6
	mov r15d, r8d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r11d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r14d, r8d
	xor r14d, r10d
	add r11d, r14d
	add r11d, -272742522
	add r11d, r13d
	add ebp, r11d
	mov r14d, r12d
	ror r14d, 2
	mov r15d, r12d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r11d, r14d
	mov r14d, r12d
	or r14d, eax
	and r14d, ebx
	mov r15d, r12d
	and r15d, eax
	or r14d, r15d
	add r11d, r14d
	mov r14d, DWORD PTR [rcx]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+44]
	mov r14d, DWORD PTR [rcx+12]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+8]
	mov DWORD PTR [rcx+8], r13d
	mov r14d, ebp
	ror r14d, 6
	mov r15d, ebp
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r8d
	xor r14d, r9d
	and r14d, ebp
	xor r14d, r9d
	add r10d, r14d
	add r10d, 264347078
	add r10d, r13d
	add ebx, r10d
	mov r14d, r11d
	ror r14d, 2
	mov r15d, r11d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	or r14d, r12d
	and r14d, eax
	mov r15d, r11d
	and r15d, r12d
	or r14d, r15d
	add r10d, r14d
	mov r14d, DWORD PTR [rcx+4]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+48]
	mov r14d, DWORD PTR [rcx+16]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+12]
	mov DWORD PTR [rcx+12], r13d
	mov r14d, ebx
	ror r14d, 6
	mov r15d, ebx
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r9d, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r14d, ebx
	xor r14d, r8d
	add r9d, r14d
	add r9d, 604807628
	add r9d, r13d
	add eax, r9d
	mov r14d, r10d
	ror r14d, 2
	mov r15d, r10d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r9d, r14d
	mov r14d, r10d
	or r14d, r11d
	and r14d, r12d
	mov r15d, r10d
	and r15d, r11d
	or r14d, r15d
	add r9d, r14d
	mov r14d, DWORD PTR [rcx+8]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+52]
	mov r14d, DWORD PTR [rcx+20]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+16]
	mov DWORD PTR [rcx+16], r13d
	mov r14d, eax
	ror r14d, 6
	mov r15d, eax
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r8d, r14d
	mov r14d, ebx
	xor r14d, ebp
	and r14d, eax
	xor r14d, ebp
	add r8d, r14d
	add r8d, 770255983
	add r8d, r13d
	add r12d, r8d
	mov r14d, r9d
	ror r14d, 2
	mov r15d, r9d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	or r14d, r10d
	and r14d, r11d
	mov r15d, r9d
	and r15d, r10d
	or r14d, r15d
	add r8d, r14d
	mov r14d, DWORD PTR [rcx+12]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+56]
	mov r14d, DWORD PTR [rcx+24]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+20]
	mov DWORD PTR [rcx+20], r13d
	mov r14d, r12d
	ror r14d, 6
	mov r15d, r12d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add ebp, r14d
	mov r14d, eax
	xor r14d, ebx
	and r14d, r12d
	xor r14d, ebx
	add ebp, r14d
	add ebp, 1249150122
	add ebp, r13d
	add r11d, ebp
	mov r14d, r8d
	ror r14d, 2
	mov r15d, r8d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add ebp, r14d
	mov r14d, r8d
	or r14d, r9d
	and r14d, r10d
	mov r15d, r8d
	and r15d, r9d
	or r14d, r15d
	add ebp, r14d
	mov r14d, DWORD PTR [rcx+16]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+60]
	mov r14d, DWORD PTR [rcx+28]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+24]
	mov DWORD PTR [rcx+24], r13d
	mov r14d, r11d
	ror r14d, 6
	mov r15d, r11d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add ebx, r14d
	mov r14d, r12d
	xor r14d, eax
	and r14d, r11d
	xor r14d, eax
	add ebx, r14d
	add ebx, 1555081692
	add ebx, r13d
	add r10d, ebx
	mov r14d, ebp
	ror r14d, 2
	mov r15d, ebp
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	or r14d, r8d
	and r14d, r9d
	mov r15d, ebp
	and r15d, r8d
	or r14d, r15d
	add ebx, r14d
	mov r14d, DWORD PTR [rcx+20]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx]
	mov r14d, DWORD PTR [rcx+32]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+28]
	mov DWORD PTR [rcx+28], r13d
	mov r14d, r10d
	ror r14d, 6
	mov r15d, r10d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add eax, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r14d, r10d
	xor r14d, r12d
	add eax, r14d
	add eax, 1996064986
	add eax, r13d
	add r9d, eax
	mov r14d, ebx
	ror r14d, 2
	mov r15d, ebx
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add eax, r14d
	mov r14d, ebx
	or r14d, ebp
	and r14d, r8d
	mov r15d, ebx
	and r15d, ebp
	or r14d, r15d
	add eax, r14d
	mov r14d, DWORD PTR [rcx+24]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+4]
	mov r14d, DWORD PTR [rcx+36]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+32]
	mov DWORD PTR [rcx+32], r13d
	mov r14d, r9d
	ror r14d, 6
	mov r15d, r9d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r12d, r14d
	mov r14d, r10d
	xor r14d, r11d
	and r14d, r9d
	xor r14d, r11d
	add r12d, r14d
	add r12d, -1740746414
	add r12d, r13d
	add r8d, r12d
	mov r14d, eax
	ror r14d, 2
	mov r15d, eax
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	or r14d, ebx
	and r14d, ebp
	mov r15d, eax
	and r15d, ebx
	or r14d, r15d
	add r12d, r14d
	mov r14d, DWORD PTR [rcx+28]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+8]
	mov r14d, DWORD PTR [rcx+40]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+36]
	mov DWORD PTR [rcx+36], r13d
	mov r14d, r8d
	ror r14d, 6
	mov r15d, r8d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r11d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r14d, r8d
	xor r14d, r10d
	add r11d, r14d
	add r11d, -1473132947
	add r11d, r13d
	add ebp, r11d
	mov r14d, r12d
	ror r14d, 2
	mov r15d, r12d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r11d, r14d
	mov r14d, r12d
	or r14d, eax
	and r14d, ebx
	mov r15d, r12d
	and r15d, eax
	or r14d, r15d
	add r11d, r14d
	mov r14d, DWORD PTR [rcx+32]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+12]
	mov r14d, DWORD PTR [rcx+44]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+40]
	mov DWORD PTR [rcx+40], r13d
	mov r14d, ebp
	ror r14d, 6
	mov r15d, ebp
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r8d
	xor r14d, r9d
	and r14d, ebp
	xor r14d, r9d
	add r10d, r14d
	add r10d, -1341970488
	add r10d, r13d
	add ebx, r10d
	mov r14d, r11d
	ror r14d, 2
	mov r15d, r11d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	or r14d, r12d
	and r14d, eax
	mov r15d, r11d
	and r15d, r12d
	or r14d, r15d
	add r10d, r14d
	mov r14d, DWORD PTR [rcx+36]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+16]
	mov r14d, DWORD PTR [rcx+48]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+44]
	mov DWORD PTR [rcx+44], r13d
	mov r14d, ebx
	ror r14d, 6
	mov r15d, ebx
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r9d, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r14d, ebx
	xor r14d, r8d
	add r9d, r14d
	add r9d, -1084653625
	add r9d, r13d
	add eax, r9d
	mov r14d, r10d
	ror r14d, 2
	mov r15d, r10d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r9d, r14d
	mov r14d, r10d
	or r14d, r11d
	and r14d, r12d
	mov r15d, r10d
	and r15d, r11d
	or r14d, r15d
	add r9d, r14d
	mov r14d, DWORD PTR [rcx+40]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+20]
	mov r14d, DWORD PTR [rcx+52]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+48]
	mov DWORD PTR [rcx+48], r13d
	mov r14d, eax
	ror r14d, 6
	mov r15d, eax
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r8d, r14d
	mov r14d, ebx
	xor r14d, ebp
	and r14d, eax
	xor r14d, ebp
	add r8d, r14d
	add r8d, -958395405
	add r8d, r13d
	add r12d, r8d
	mov r14d, r9d
	ror r14d, 2
	mov r15d, r9d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	or r14d, r10d
	and r14d, r11d
	mov r15d, r9d
	and r15d, r10d
	or r14d, r15d
	add r8d, r14d
	mov r14d, DWORD PTR [rcx+44]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+24]
	mov r14d, DWORD PTR [rcx+56]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+52]
	mov DWORD PTR [rcx+52], r13d
	mov r14d, r12d
	ror r14d, 6
	mov r15d, r12d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add ebp, r14d
	mov r14d, eax
	xor r14d, ebx
	and r14d, r12d
	xor r14d, ebx
	add ebp, r14d
	add ebp, -710438585
	add ebp, r13d
	add r11d, ebp
	mov r14d, r8d
	ror r14d, 2
	mov r15d, r8d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add ebp, r14d
	mov r14d, r8d
	or r14d, r9d
	and r14d, r10d
	mov r15d, r8d
	and r15d, r9d
	or r14d, r15d
	add ebp, r14d
	mov r14d, DWORD PTR [rcx+48]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+28]
	mov r14d, DWORD PTR [rcx+60]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+56]
	mov DWORD PTR [rcx+56], r13d
	mov r14d, r11d
	ror r14d, 6
	mov r15d, r11d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add ebx, r14d
	mov r14d, r12d
	xor r14d, eax
	and r14d, r11d
	xor r14d, eax
	add ebx, r14d
	add ebx, 113926993
	add ebx, r13d
	add r10d, ebx
	mov r14d, ebp
	ror r14d, 2
	mov r15d, ebp
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	or r14d, r8d
	and r14d, r9d
	mov r15d, ebp
	and r15d, r8d
	or r14d, r15d
	add ebx, r14d
	mov r14d, DWORD PTR [rcx+52]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+32]
	mov r14d, DWORD PTR [rcx]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+60]
	mov DWORD PTR [rcx+60], r13d
	mov r14d, r10d
	ror r14d, 6
	mov r15d, r10d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add eax, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r14d, r10d
	xor r14d, r12d
	add eax, r14d
	add eax, 338241895
	add eax, r13d
	add r9d, eax
	mov r14d, ebx
	ror r14d, 2
	mov r15d, ebx
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add eax, r14d
	mov r14d, ebx
	or r14d, ebp
	and r14d, r8d
	mov r15d, ebx
	and r15d, ebp
	or r14d, r15d
	add eax, r14d
	mov r14d, DWORD PTR [rcx+56]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+36]
	mov r14d, DWORD PTR [rcx+4]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx]
	mov DWORD PTR [rcx], r13d
	mov r14d, r9d
	ror r14d, 6
	mov r15d, r9d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r12d, r14d
	mov r14d, r10d
	xor r14d, r11d
	and r14d, r9d
	xor r14d, r11d
	add r12d, r14d
	add r12d, 666307205
	add r12d, r13d
	add r8d, r12d
	mov r14d, eax
	ror r14d, 2
	mov r15d, eax
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	or r14d, ebx
	and r14d, ebp
	mov r15d, eax
	and r15d, ebx
	or r14d, r15d
	add r12d, r14d
	mov r14d, DWORD PTR [rcx+60]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+40]
	mov r14d, DWORD PTR [rcx+8]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+4]
	mov DWORD PTR [rcx+4], r13d
	mov r14d, r8d
	ror r14d, 6
	mov r15d, r8d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r11d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r14d, r8d
	xor r14d, r10d
	add r11d, r14d
	add r11d, 773529912
	add r11d, r13d
	add ebp, r11d
	mov r14d, r12d
	ror r14d, 2
	mov r15d, r12d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r11d, r14d
	mov r14d, r12d
	or r14d, eax
	and r14d, ebx
	mov r15d, r12d
	and r15d, eax
	or r14d, r15d
	add r11d, r14d
	mov r14d, DWORD PTR [rcx]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+44]
	mov r14d, DWORD PTR [rcx+12]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+8]
	mov DWORD PTR [rcx+8], r13d
	mov r14d, ebp
	ror r14d, 6
	mov r15d, ebp
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r8d
	xor r14d, r9d
	and r14d, ebp
	xor r14d, r9d
	add r10d, r14d
	add r10d, 1294757372
	add r10d, r13d
	add ebx, r10d
	mov r14d, r11d
	ror r14d, 2
	mov r15d, r11d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	or r14d, r12d
	and r14d, eax
	mov r15d, r11d
	and r15d, r12d
	or r14d, r15d
	add r10d, r14d
	mov r14d, DWORD PTR [rcx+4]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+48]
	mov r14d, DWORD PTR [rcx+16]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+12]
	mov DWORD PTR [rcx+12], r13d
	mov r14d, ebx
	ror r14d, 6
	mov r15d, ebx
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r9d, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r14d, ebx
	xor r14d, r8d
	add r9d, r14d
	add r9d, 1396182291
	add r9d, r13d
	add eax, r9d
	mov r14d, r10d
	ror r14d, 2
	mov r15d, r10d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r9d, r14d
	mov r14d, r10d
	or r14d, r11d
	and r14d, r12d
	mov r15d, r10d
	and r15d, r11d
	or r14d, r15d
	add r9d, r14d
	mov r14d, DWORD PTR [rcx+8]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+52]
	mov r14d, DWORD PTR [rcx+20]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+16]
	mov DWORD PTR [rcx+16], r13d
	mov r14d, eax
	ror r14d, 6
	mov r15d, eax
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r8d, r14d
	mov r14d, ebx
	xor r14d, ebp
	and r14d, eax
	xor r14d, ebp
	add r8d, r14d
	add r8d, 1695183700
	add r8d, r13d
	add r12d, r8d
	mov r14d, r9d
	ror r14d, 2
	mov r15d, r9d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	or r14d, r10d
	and r14d, r11d
	mov r15d, r9d
	and r15d, r10d
	or r14d, r15d
	add r8d, r14d
	mov r14d, DWORD PTR [rcx+12]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+56]
	mov r14d, DWORD PTR [rcx+24]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+20]
	mov DWORD PTR [rcx+20], r13d
	mov r14d, r12d
	ror r14d, 6
	mov r15d, r12d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add ebp, r14d
	mov r14d, eax
	xor r14d, ebx
	and r14d, r12d
	xor r14d, ebx
	add ebp, r14d
	add ebp, 1986661051
	add ebp, r13d
	add r11d, ebp
	mov r14d, r8d
	ror r14d, 2
	mov r15d, r8d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add ebp, r14d
	mov r14d, r8d
	or r14d, r9d
	and r14d, r10d
	mov r15d, r8d
	and r15d, r9d
	or r14d, r15d
	add ebp, r14d
	mov r14d, DWORD PTR [rcx+16]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+60]
	mov r14d, DWORD PTR [rcx+28]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+24]
	mov DWORD PTR [rcx+24], r13d
	mov r14d, r11d
	ror r14d, 6
	mov r15d, r11d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add ebx, r14d
	mov r14d, r12d
	xor r14d, eax
	and r14d, r11d
	xor r14d, eax
	add ebx, r14d
	add ebx, -2117940946
	add ebx, r13d
	add r10d, ebx
	mov r14d, ebp
	ror r14d, 2
	mov r15d, ebp
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	or r14d, r8d
	and r14d, r9d
	mov r15d, ebp
	and r15d, r8d
	or r14d, r15d
	add ebx, r14d
	mov r14d, DWORD PTR [rcx+20]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx]
	mov r14d, DWORD PTR [rcx+32]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+28]
	mov DWORD PTR [rcx+28], r13d
	mov r14d, r10d
	ror r14d, 6
	mov r15d, r10d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add eax, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r14d, r10d
	xor r14d, r12d
	add eax, r14d
	add eax, -1838011259
	add eax, r13d
	add r9d, eax
	mov r14d, ebx
	ror r14d, 2
	mov r15d, ebx
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add eax, r14d
	mov r14d, ebx
	or r14d, ebp
	and r14d, r8d
	mov r15d, ebx
	and r15d, ebp
	or r14d, r15d
	add eax, r14d
	mov r14d, DWORD PTR [rcx+24]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+4]
	mov r14d, DWORD PTR [rcx+36]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+32]
	mov DWORD PTR [rcx+32], r13d
	mov r14d, r9d
	ror r14d, 6
	mov r15d, r9d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r12d, r14d
	mov r14d, r10d
	xor r14d, r11d
	and r14d, r9d
	xor r14d, r11d
	add r12d, r14d
	add r12d, -1564481375
	add r12d, r13d
	add r8d, r12d
	mov r14d, eax
	ror r14d, 2
	mov r15d, eax
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	or r14d, ebx
	and r14d, ebp
	mov r15d, eax
	and r15d, ebx
	or r14d, r15d
	add r12d, r14d
	mov r14d, DWORD PTR [rcx+28]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+8]
	mov r14d, DWORD PTR [rcx+40]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+36]
	mov DWORD PTR [rcx+36], r13d
	mov r14d, r8d
	ror r14d, 6
	mov r15d, r8d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r11d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r14d, r8d
	xor r14d, r10d
	add r11d, r14d
	add r11d, -1474664885
	add r11d, r13d
	add ebp, r11d
	mov r14d, r12d
	ror r14d, 2
	mov r15d, r12d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r11d, r14d
	mov r14d, r12d
	or r14d, eax
	and r14d, ebx
	mov r15d, r12d
	and r15d, eax
	or r14d, r15d
	add r11d, r14d
	mov r14d, DWORD PTR [rcx+32]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+12]
	mov r14d, DWORD PTR [rcx+44]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+40]
	mov DWORD PTR [rcx+40], r13d
	mov r14d, ebp
	ror r14d, 6
	mov r15d, ebp
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r8d
	xor r14d, r9d
	and r14d, ebp
	xor r14d, r9d
	add r10d, r14d
	add r10d, -1035236496
	add r10d, r13d
	add ebx, r10d
	mov r14d, r11d
	ror r14d, 2
	mov r15d, r11d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	or r14d, r12d
	and r14d, eax
	mov r15d, r11d
	and r15d, r12d
	or r14d, r15d
	add r10d, r14d
	mov r14d, DWORD PTR [rcx+36]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+16]
	mov r14d, DWORD PTR [rcx+48]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+44]
	mov DWORD PTR [rcx+44], r13d
	mov r14d, ebx
	ror r14d, 6
	mov r15d, ebx
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r9d, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r14d, ebx
	xor r14d, r8d
	add r9d, r14d
	add r9d, -949202525
	add r9d, r13d
	add eax, r9d
	mov r14d, r10d
	ror r14d, 2
	mov r15d, r10d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r9d, r14d
	mov r14d, r10d
	or r14d, r11d
	and r14d, r12d
	mov r15d, r10d
	and r15d, r11d
	or r14d, r15d
	add r9d, r14d
	mov r14d, DWORD PTR [rcx+40]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+20]
	mov r14d, DWORD PTR [rcx+52]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+48]
	mov DWORD PTR [rcx+48], r13d
	mov r14d, eax
	ror r14d, 6
	mov r15d, eax
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r8d, r14d
	mov r14d, ebx
	xor r14d, ebp
	and r14d, eax
	xor r14d, ebp
	add r8d, r14d
	add r8d, -778901479
	add r8d, r13d
	add r12d, r8d
	mov r14d, r9d
	ror r14d, 2
	mov r15d, r9d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	or r14d, r10d
	and r14d, r11d
	mov r15d, r9d
	and r15d, r10d
	or r14d, r15d
	add r8d, r14d
	mov r14d, DWORD PTR [rcx+44]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+24]
	mov r14d, DWORD PTR [rcx+56]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+52]
	mov DWORD PTR [rcx+52], r13d
	mov r14d, r12d
	ror r14d, 6
	mov r15d, r12d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add ebp, r14d
	mov r14d, eax
	xor r14d, ebx
	and r14d, r12d
	xor r14d, ebx
	add ebp, r14d
	add ebp, -694614492
	add ebp, r13d
	add r11d, ebp
	mov r14d, r8d
	ror r14d, 2
	mov r15d, r8d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add ebp, r14d
	mov r14d, r8d
	or r14d, r9d
	and r14d, r10d
	mov r15d, r8d
	and r15d, r9d
	or r14d, r15d
	add ebp, r14d
	mov r14d, DWORD PTR [rcx+48]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+28]
	mov r14d, DWORD PTR [rcx+60]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+56]
	mov DWORD PTR [rcx+56], r13d
	mov r14d, r11d
	ror r14d, 6
	mov r15d, r11d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add ebx, r14d
	mov r14d, r12d
	xor r14d, eax
	and r14d, r11d
	xor r14d, eax
	add ebx, r14d
	add ebx, -200395387
	add ebx, r13d
	add r10d, ebx
	mov r14d, ebp
	ror r14d, 2
	mov r15d, ebp
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	or r14d, r8d
	and r14d, r9d
	mov r15d, ebp
	and r15d, r8d
	or r14d, r15d
	add ebx, r14d
	mov r14d, DWORD PTR [rcx+52]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+32]
	mov r14d, DWORD PTR [rcx]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+60]
	mov DWORD PTR [rcx+60], r13d
	mov r14d, r10d
	ror r14d, 6
	mov r15d, r10d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add eax, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r14d, r10d
	xor r14d, r12d
	add eax, r14d
	add eax, 275423344
	add eax, r13d
	add r9d, eax
	mov r14d, ebx
	ror r14d, 2
	mov r15d, ebx
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add eax, r14d
	mov r14d, ebx
	or r14d, ebp
	and r14d, r8d
	mov r15d, ebx
	and r15d, ebp
	or r14d, r15d
	add eax, r14d
	mov r14d, DWORD PTR [rcx+56]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+36]
	mov r14d, DWORD PTR [rcx+4]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx]
	mov DWORD PTR [rcx], r13d
	mov r14d, r9d
	ror r14d, 6
	mov r15d, r9d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r12d, r14d
	mov r14d, r10d
	xor r14d, r11d
	and r14d, r9d
	xor r14d, r11d
	add r12d, r14d
	add r12d, 430227734
	add r12d, r13d
	add r8d, r12d
	mov r14d, eax
	ror r14d, 2
	mov r15d, eax
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	or r14d, ebx
	and r14d, ebp
	mov r15d, eax
	and r15d, ebx
	or r14d, r15d
	add r12d, r14d
	mov r14d, DWORD PTR [rcx+60]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+40]
	mov r14d, DWORD PTR [rcx+8]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+4]
	mov DWORD PTR [rcx+4], r13d
	mov r14d, r8d
	ror r14d, 6
	mov r15d, r8d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r11d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r14d, r8d
	xor r14d, r10d
	add r11d, r14d
	add r11d, 506948616
	add r11d, r13d
	add ebp, r11d
	mov r14d, r12d
	ror r14d, 2
	mov r15d, r12d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r11d, r14d
	mov r14d, r12d
	or r14d, eax
	and r14d, ebx
	mov r15d, r12d
	and r15d, eax
	or r14d, r15d
	add r11d, r14d
	mov r14d, DWORD PTR [rcx]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+44]
	mov r14d, DWORD PTR [rcx+12]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+8]
	mov DWORD PTR [rcx+8], r13d
	mov r14d, ebp
	ror r14d, 6
	mov r15d, ebp
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r8d
	xor r14d, r9d
	and r14d, ebp
	xor r14d, r9d
	add r10d, r14d
	add r10d, 659060556
	add r10d, r13d
	add ebx, r10d
	mov r14d, r11d
	ror r14d, 2
	mov r15d, r11d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	or r14d, r12d
	and r14d, eax
	mov r15d, r11d
	and r15d, r12d
	or r14d, r15d
	add r10d, r14d
	mov r14d, DWORD PTR [rcx+4]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+48]
	mov r14d, DWORD PTR [rcx+16]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+12]
	mov DWORD PTR [rcx+12], r13d
	mov r14d, ebx
	ror r14d, 6
	mov r15d, ebx
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r9d, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r14d, ebx
	xor r14d, r8d
	add r9d, r14d
	add r9d, 883997877
	add r9d, r13d
	add eax, r9d
	mov r14d, r10d
	ror r14d, 2
	mov r15d, r10d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r9d, r14d
	mov r14d, r10d
	or r14d, r11d
	and r14d, r12d
	mov r15d, r10d
	and r15d, r11d
	or r14d, r15d
	add r9d, r14d
	mov r14d, DWORD PTR [rcx+8]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+52]
	mov r14d, DWORD PTR [rcx+20]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+16]
	mov DWORD PTR [rcx+16], r13d
	mov r14d, eax
	ror r14d, 6
	mov r15d, eax
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r8d, r14d
	mov r14d, ebx
	xor r14d, ebp
	and r14d, eax
	xor r14d, ebp
	add r8d, r14d
	add r8d, 958139571
	add r8d, r13d
	add r12d, r8d
	mov r14d, r9d
	ror r14d, 2
	mov r15d, r9d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	or r14d, r10d
	and r14d, r11d
	mov r15d, r9d
	and r15d, r10d
	or r14d, r15d
	add r8d, r14d
	mov r14d, DWORD PTR [rcx+12]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+56]
	mov r14d, DWORD PTR [rcx+24]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+20]
	mov DWORD PTR [rcx+20], r13d
	mov r14d, r12d
	ror r14d, 6
	mov r15d, r12d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add ebp, r14d
	mov r14d, eax
	xor r14d, ebx
	and r14d, r12d
	xor r14d, ebx
	add ebp, r14d
	add ebp, 1322822218
	add ebp, r13d
	add r11d, ebp
	mov r14d, r8d
	ror r14d, 2
	mov r15d, r8d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add ebp, r14d
	mov r14d, r8d
	or r14d, r9d
	and r14d, r10d
	mov r15d, r8d
	and r15d, r9d
	or r14d, r15d
	add ebp, r14d
	mov r14d, DWORD PTR [rcx+16]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+60]
	mov r14d, DWORD PTR [rcx+28]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+24]
	mov DWORD PTR [rcx+24], r13d
	mov r14d, r11d
	ror r14d, 6
	mov r15d, r11d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add ebx, r14d
	mov r14d, r12d
	xor r14d, eax
	and r14d, r11d
	xor r14d, eax
	add ebx, r14d
	add ebx, 1537002063
	add ebx, r13d
	add r10d, ebx
	mov r14d, ebp
	ror r14d, 2
	mov r15d, ebp
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	or r14d, r8d
	and r14d, r9d
	mov r15d, ebp
	and r15d, r8d
	or r14d, r15d
	add ebx, r14d
	mov r14d, DWORD PTR [rcx+20]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx]
	mov r14d, DWORD PTR [rcx+32]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+28]
	mov DWORD PTR [rcx+28], r13d
	mov r14d, r10d
	ror r14d, 6
	mov r15d, r10d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add eax, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r14d, r10d
	xor r14d, r12d
	add eax, r14d
	add eax, 1747873779
	add eax, r13d
	add r9d, eax
	mov r14d, ebx
	ror r14d, 2
	mov r15d, ebx
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add eax, r14d
	mov r14d, ebx
	or r14d, ebp
	and r14d, r8d
	mov r15d, ebx
	and r15d, ebp
	or r14d, r15d
	add eax, r14d
	mov r14d, DWORD PTR [rcx+24]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+4]
	mov r14d, DWORD PTR [rcx+36]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+32]
	mov DWORD PTR [rcx+32], r13d
	mov r14d, r9d
	ror r14d, 6
	mov r15d, r9d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r12d, r14d
	mov r14d, r10d
	xor r14d, r11d
	and r14d, r9d
	xor r14d, r11d
	add r12d, r14d
	add r12d, 1955562222
	add r12d, r13d
	add r8d, r12d
	mov r14d, eax
	ror r14d, 2
	mov r15d, eax
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	or r14d, ebx
	and r14d, ebp
	mov r15d, eax
	and r15d, ebx
	or r14d, r15d
	add r12d, r14d
	mov r14d, DWORD PTR [rcx+28]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+8]
	mov r14d, DWORD PTR [rcx+40]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+36]
	mov DWORD PTR [rcx+36], r13d
	mov r14d, r8d
	ror r14d, 6
	mov r15d, r8d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r11d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r14d, r8d
	xor r14d, r10d
	add r11d, r14d
	add r11d, 2024104815
	add r11d, r13d
	add ebp, r11d
	mov r14d, r12d
	ror r14d, 2
	mov r15d, r12d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r11d, r14d
	mov r14d, r12d
	or r14d, eax
	and r14d, ebx
	mov r15d, r12d
	and r15d, eax
	or r14d, r15d
	add r11d, r14d
	mov r14d, DWORD PTR [rcx+32]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+12]
	mov r14d, DWORD PTR [rcx+44]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+40]
	mov DWORD PTR [rcx+40], r13d
	mov r14d, ebp
	ror r14d, 6
	mov r15d, ebp
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r8d
	xor r14d, r9d
	and r14d, ebp
	xor r14d, r9d
	add r10d, r14d
	add r10d, -2067236844
	add r10d, r13d
	add ebx, r10d
	mov r14d, r11d
	ror r14d, 2
	mov r15d, r11d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	or r14d, r12d
	and r14d, eax
	mov r15d, r11d
	and r15d, r12d
	or r14d, r15d
	add r10d, r14d
	mov r14d, DWORD PTR [rcx+36]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+16]
	mov r14d, DWORD PTR [rcx+48]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+44]
	mov DWORD PTR [rcx+44], r13d
	mov r14d, ebx
	ror r14d, 6
	mov r15d, ebx
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r9d, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r14d, ebx
	xor r14d, r8d
	add r9d, r14d
	add r9d, -1933114872
	add r9d, r13d
	add eax, r9d
	mov r14d, r10d
	ror r14d, 2
	mov r15d, r10d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r9d, r14d
	mov r14d, r10d
	or r14d, r11d
	and r14d, r12d
	mov r15d, r10d
	and r15d, r11d
	or r14d, r15d
	add r9d, r14d
	mov r14d, DWORD PTR [rcx+40]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+20]
	mov r14d, DWORD PTR [rcx+52]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+48]
	mov DWORD PTR [rcx+48], r13d
	mov r14d, eax
	ror r14d, 6
	mov r15d, eax
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add r8d, r14d
	mov r14d, ebx
	xor r14d, ebp
	and r14d, eax
	xor r14d, ebp
	add r8d, r14d
	add r8d, -1866530822
	add r8d, r13d
	add r12d, r8d
	mov r14d, r9d
	ror r14d, 2
	mov r15d, r9d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	or r14d, r10d
	and r14d, r11d
	mov r15d, r9d
	and r15d, r10d
	or r14d, r15d
	add r8d, r14d
	mov r14d, DWORD PTR [rcx+44]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+24]
	mov r14d, DWORD PTR [rcx+56]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+52]
	mov DWORD PTR [rcx+52], r13d
	mov r14d, r12d
	ror r14d, 6
	mov r15d, r12d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add ebp, r14d
	mov r14d, eax
	xor r14d, ebx
	and r14d, r12d
	xor r14d, ebx
	add ebp, r14d
	add ebp, -1538233109
	add ebp, r13d
	add r11d, ebp
	mov r14d, r8d
	ror r14d, 2
	mov r15d, r8d
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add ebp, r14d
	mov r14d, r8d
	or r14d, r9d
	and r14d, r10d
	mov r15d, r8d
	and r15d, r9d
	or r14d, r15d
	add ebp, r14d
	mov r14d, DWORD PTR [rcx+48]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+28]
	mov r14d, DWORD PTR [rcx+60]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+56]
	mov DWORD PTR [rcx+56], r13d
	mov r14d, r11d
	ror r14d, 6
	mov r15d, r11d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add ebx, r14d
	mov r14d, r12d
	xor r14d, eax
	and r14d, r11d
	xor r14d, eax
	add ebx, r14d
	add ebx, -1090935817
	add ebx, r13d
	add r10d, ebx
	mov r14d, ebp
	ror r14d, 2
	mov r15d, ebp
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	or r14d, r8d
	and r14d, r9d
	mov r15d, ebp
	and r15d, r8d
	or r14d, r15d
	add ebx, r14d
	mov r14d, DWORD PTR [rcx+52]
	mov r13d, r14d
	ror r13d, 2
	xor r13d, r14d
	ror r13d, 17
	shr r14d, 10
	xor r13d, r14d
	add r13d, DWORD PTR [rcx+32]
	mov r14d, DWORD PTR [rcx]
	mov r15d, r14d
	ror r15d, 11
	xor r15d, r14d
	ror r15d, 7
	shr r14d, 3
	xor r15d, r14d
	add r13d, r15d
	add r13d, DWORD PTR [rcx+60]
	mov DWORD PTR [rcx+60], r13d
	mov r14d, r10d
	ror r14d, 6
	mov r15d, r10d
	ror r15d, 11
	xor r14d, r15d
	ror r15d, 14
	xor r14d, r15d
	add eax, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r14d, r10d
	xor r14d, r12d
	add eax, r14d
	add eax, -965641998
	add eax, r13d
	add r9d, eax
	mov r14d, ebx
	ror r14d, 2
	mov r15d, ebx
	ror r15d, 13
	xor r14d, r15d
	ror r15d, 9
	xor r14d, r15d
	add eax, r14d
	mov r14d, ebx
	or r14d, ebp
	and r14d, r8d
	mov r15d, ebx
	and r15d, ebp
	or r14d, r15d
	add eax, r14d
	add eax, DWORD PTR [rdi]
	add ebx, DWORD PTR [rdi+4]
	add ebp, DWORD PTR [rdi+8]
	add r8d, DWORD PTR [rdi+12]
	add r9d, DWORD PTR [rdi+16]
	add r10d, DWORD PTR [rdi+20]
	add r11d, DWORD PTR [rdi+24]
	add r12d, DWORD PTR [rdi+28]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+4], ebx
	mov DWORD PTR [rdi+8], ebp
	mov DWORD PTR [rdi+12], r8d
	mov DWORD PTR [rdi+16], r9d
	mov DWORD PTR [rdi+20], r10d
	mov DWORD PTR [rdi+24], r11d
	mov DWORD PTR [rdi+28], r12d
	add rsi, 64
	sub rdx, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [rcx+64]
	mov rbp, QWORD PTR [rcx+72]
	mov r12, QWORD PTR [rcx+80]
	mov r13, QWORD PTR [rcx+88]
	mov r14, QWORD PTR [rcx+96]
	mov r15, QWORD PTR [rcx+104]
	ret
	.p2align 6

vg_sha256_init:
	movabs rax, -4942790177982912921
	movq xmm0, rax
	movabs rax, -6534734903820487822
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	movabs rax, -7276294671082564993
	movq xmm0, rax
	movabs rax, 6620516960021240235
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi+16], xmm0
	ret
	.p2align 6

vg_sha256_compress_shani:
	lea rax, {VG_SHA256_SHANI_K}
	movdqu xmm8, XMMWORD PTR [rax+256]
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+16]
	pshufd xmm1, xmm1, 177
	pshufd xmm2, xmm2, 177
	movdqa xmm7, xmm2
	punpcklqdq xmm7, xmm1
	punpckhqdq xmm2, xmm1
	movdqa xmm1, xmm7
	test rdx, rdx
	je 20f
22:
	movdqa xmm9, xmm1
	movdqa xmm10, xmm2
	movdqu xmm3, XMMWORD PTR [rsi]
	pshufb xmm3, xmm8
	movdqu xmm0, XMMWORD PTR [rax]
	paddd xmm0, xmm3
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm4, XMMWORD PTR [rsi+16]
	pshufb xmm4, xmm8
	movdqu xmm0, XMMWORD PTR [rax+16]
	paddd xmm0, xmm4
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm5, XMMWORD PTR [rsi+32]
	pshufb xmm5, xmm8
	movdqu xmm0, XMMWORD PTR [rax+32]
	paddd xmm0, xmm5
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [rsi+48]
	pshufb xmm6, xmm8
	movdqu xmm0, XMMWORD PTR [rax+48]
	paddd xmm0, xmm6
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqu xmm0, XMMWORD PTR [rax+64]
	paddd xmm0, xmm3
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqu xmm0, XMMWORD PTR [rax+80]
	paddd xmm0, xmm4
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqu xmm0, XMMWORD PTR [rax+96]
	paddd xmm0, xmm5
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [rax+112]
	paddd xmm0, xmm6
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqu xmm0, XMMWORD PTR [rax+128]
	paddd xmm0, xmm3
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqu xmm0, XMMWORD PTR [rax+144]
	paddd xmm0, xmm4
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqu xmm0, XMMWORD PTR [rax+160]
	paddd xmm0, xmm5
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [rax+176]
	paddd xmm0, xmm6
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqu xmm0, XMMWORD PTR [rax+192]
	paddd xmm0, xmm3
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqu xmm0, XMMWORD PTR [rax+208]
	paddd xmm0, xmm4
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqu xmm0, XMMWORD PTR [rax+224]
	paddd xmm0, xmm5
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [rax+240]
	paddd xmm0, xmm6
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	paddd xmm1, xmm9
	paddd xmm2, xmm10
	add rsi, 64
	sub rdx, 1
	jne 22b
	jmp 21f
20:
21:
	movdqa xmm7, xmm1
	punpckhqdq xmm7, xmm2
	punpcklqdq xmm1, xmm2
	pshufd xmm7, xmm7, 177
	pshufd xmm1, xmm1, 177
	movdqu XMMWORD PTR [rdi], xmm7
	movdqu XMMWORD PTR [rdi+16], xmm1
	ret
	.p2align 6

vg_sha256_compress_avx2:
	mov QWORD PTR [rcx+512], rbx
	mov QWORD PTR [rcx+520], rbp
	mov QWORD PTR [rcx+528], r12
	mov QWORD PTR [rcx+536], r13
	mov QWORD PTR [rcx+544], r14
	mov QWORD PTR [rcx+552], r15
	movabs rax, 289644378169868803
	vmovq xmm10, rax
	movabs rax, 868365760874482187
	vmovq xmm11, rax
	vpunpcklqdq xmm10, xmm10, xmm11
	vinserti128 ymm10, ymm10, xmm10, 1
	movabs rax, 795458214199165184
	vmovq xmm8, rax
	movabs rax, -1
	vmovq xmm11, rax
	vpunpcklqdq xmm8, xmm8, xmm11
	vinserti128 ymm8, ymm8, xmm8, 1
	movabs rax, -1
	vmovq xmm9, rax
	movabs rax, 795458214199165184
	vmovq xmm11, rax
	vpunpcklqdq xmm9, xmm9, xmm11
	vinserti128 ymm9, ymm9, xmm9, 1
	test rdx, rdx
	je 20f
22:
	mov r15, rsi
	cmp rdx, 1
	je 23f
	add r15, 64
	jmp 24f
23:
24:
	vmovdqu xmm0, XMMWORD PTR [rsi]
	vmovdqu xmm11, XMMWORD PTR [r15]
	vinserti128 ymm0, ymm0, xmm11, 1
	vpshufb ymm0, ymm0, ymm10
	vmovdqu YMMWORD PTR [rcx], ymm0
	vmovdqu xmm1, XMMWORD PTR [rsi+16]
	vmovdqu xmm11, XMMWORD PTR [r15+16]
	vinserti128 ymm1, ymm1, xmm11, 1
	vpshufb ymm1, ymm1, ymm10
	vmovdqu YMMWORD PTR [rcx+32], ymm1
	vmovdqu xmm2, XMMWORD PTR [rsi+32]
	vmovdqu xmm11, XMMWORD PTR [r15+32]
	vinserti128 ymm2, ymm2, xmm11, 1
	vpshufb ymm2, ymm2, ymm10
	vmovdqu YMMWORD PTR [rcx+64], ymm2
	vmovdqu xmm3, XMMWORD PTR [rsi+48]
	vmovdqu xmm11, XMMWORD PTR [r15+48]
	vinserti128 ymm3, ymm3, xmm11, 1
	vpshufb ymm3, ymm3, ymm10
	vmovdqu YMMWORD PTR [rcx+96], ymm3
	mov eax, DWORD PTR [rdi]
	mov ebx, DWORD PTR [rdi+4]
	mov ebp, DWORD PTR [rdi+8]
	mov r8d, DWORD PTR [rdi+12]
	mov r9d, DWORD PTR [rdi+16]
	mov r10d, DWORD PTR [rdi+20]
	mov r11d, DWORD PTR [rdi+24]
	mov r12d, DWORD PTR [rdi+28]
	mov r13d, ebx
	xor r13d, ebp
	vpalignr ymm4, ymm1, ymm0, 4
	vpalignr ymm7, ymm3, ymm2, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm0, ymm0, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm3, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm0, ymm0, ymm6
	vpshufd ymm7, ymm0, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm0, ymm0, ymm6
	vmovdqu YMMWORD PTR [rcx+128], ymm0
	add r12d, 1116352408
	add r12d, DWORD PTR [rcx]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 1899447441
	add r11d, DWORD PTR [rcx+4]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, -1245643825
	add r10d, DWORD PTR [rcx+8]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, -373957723
	add r9d, DWORD PTR [rcx+12]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	vpalignr ymm4, ymm2, ymm1, 4
	vpalignr ymm7, ymm0, ymm3, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm1, ymm1, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm0, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm1, ymm1, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm1, ymm1, ymm6
	vpshufd ymm7, ymm1, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm1, ymm1, ymm6
	vmovdqu YMMWORD PTR [rcx+160], ymm1
	add r8d, 961987163
	add r8d, DWORD PTR [rcx+32]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, 1508970993
	add ebp, DWORD PTR [rcx+36]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -1841331548
	add ebx, DWORD PTR [rcx+40]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, -1424204075
	add eax, DWORD PTR [rcx+44]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	vpalignr ymm4, ymm3, ymm2, 4
	vpalignr ymm7, ymm1, ymm0, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm2, ymm2, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm1, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm2, ymm2, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm2, ymm2, ymm6
	vpshufd ymm7, ymm2, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm2, ymm2, ymm6
	vmovdqu YMMWORD PTR [rcx+192], ymm2
	add r12d, -670586216
	add r12d, DWORD PTR [rcx+64]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 310598401
	add r11d, DWORD PTR [rcx+68]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, 607225278
	add r10d, DWORD PTR [rcx+72]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, 1426881987
	add r9d, DWORD PTR [rcx+76]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	vpalignr ymm4, ymm0, ymm3, 4
	vpalignr ymm7, ymm2, ymm1, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm3, ymm3, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm2, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm3, ymm3, ymm6
	vpshufd ymm7, ymm3, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm3, ymm3, ymm6
	vmovdqu YMMWORD PTR [rcx+224], ymm3
	add r8d, 1925078388
	add r8d, DWORD PTR [rcx+96]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, -2132889090
	add ebp, DWORD PTR [rcx+100]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -1680079193
	add ebx, DWORD PTR [rcx+104]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, -1046744716
	add eax, DWORD PTR [rcx+108]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	vpalignr ymm4, ymm1, ymm0, 4
	vpalignr ymm7, ymm3, ymm2, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm0, ymm0, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm3, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm0, ymm0, ymm6
	vpshufd ymm7, ymm0, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm0, ymm0, ymm6
	vmovdqu YMMWORD PTR [rcx+256], ymm0
	add r12d, -459576895
	add r12d, DWORD PTR [rcx+128]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, -272742522
	add r11d, DWORD PTR [rcx+132]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, 264347078
	add r10d, DWORD PTR [rcx+136]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, 604807628
	add r9d, DWORD PTR [rcx+140]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	vpalignr ymm4, ymm2, ymm1, 4
	vpalignr ymm7, ymm0, ymm3, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm1, ymm1, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm0, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm1, ymm1, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm1, ymm1, ymm6
	vpshufd ymm7, ymm1, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm1, ymm1, ymm6
	vmovdqu YMMWORD PTR [rcx+288], ymm1
	add r8d, 770255983
	add r8d, DWORD PTR [rcx+160]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, 1249150122
	add ebp, DWORD PTR [rcx+164]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, 1555081692
	add ebx, DWORD PTR [rcx+168]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, 1996064986
	add eax, DWORD PTR [rcx+172]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	vpalignr ymm4, ymm3, ymm2, 4
	vpalignr ymm7, ymm1, ymm0, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm2, ymm2, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm1, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm2, ymm2, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm2, ymm2, ymm6
	vpshufd ymm7, ymm2, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm2, ymm2, ymm6
	vmovdqu YMMWORD PTR [rcx+320], ymm2
	add r12d, -1740746414
	add r12d, DWORD PTR [rcx+192]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, -1473132947
	add r11d, DWORD PTR [rcx+196]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, -1341970488
	add r10d, DWORD PTR [rcx+200]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, -1084653625
	add r9d, DWORD PTR [rcx+204]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	vpalignr ymm4, ymm0, ymm3, 4
	vpalignr ymm7, ymm2, ymm1, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm3, ymm3, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm2, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm3, ymm3, ymm6
	vpshufd ymm7, ymm3, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm3, ymm3, ymm6
	vmovdqu YMMWORD PTR [rcx+352], ymm3
	add r8d, -958395405
	add r8d, DWORD PTR [rcx+224]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, -710438585
	add ebp, DWORD PTR [rcx+228]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, 113926993
	add ebx, DWORD PTR [rcx+232]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, 338241895
	add eax, DWORD PTR [rcx+236]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	vpalignr ymm4, ymm1, ymm0, 4
	vpalignr ymm7, ymm3, ymm2, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm0, ymm0, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm3, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm0, ymm0, ymm6
	vpshufd ymm7, ymm0, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm0, ymm0, ymm6
	vmovdqu YMMWORD PTR [rcx+384], ymm0
	add r12d, 666307205
	add r12d, DWORD PTR [rcx+256]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 773529912
	add r11d, DWORD PTR [rcx+260]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, 1294757372
	add r10d, DWORD PTR [rcx+264]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, 1396182291
	add r9d, DWORD PTR [rcx+268]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	vpalignr ymm4, ymm2, ymm1, 4
	vpalignr ymm7, ymm0, ymm3, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm1, ymm1, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm0, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm1, ymm1, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm1, ymm1, ymm6
	vpshufd ymm7, ymm1, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm1, ymm1, ymm6
	vmovdqu YMMWORD PTR [rcx+416], ymm1
	add r8d, 1695183700
	add r8d, DWORD PTR [rcx+288]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, 1986661051
	add ebp, DWORD PTR [rcx+292]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -2117940946
	add ebx, DWORD PTR [rcx+296]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, -1838011259
	add eax, DWORD PTR [rcx+300]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	vpalignr ymm4, ymm3, ymm2, 4
	vpalignr ymm7, ymm1, ymm0, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm2, ymm2, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm1, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm2, ymm2, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm2, ymm2, ymm6
	vpshufd ymm7, ymm2, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm2, ymm2, ymm6
	vmovdqu YMMWORD PTR [rcx+448], ymm2
	add r12d, -1564481375
	add r12d, DWORD PTR [rcx+320]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, -1474664885
	add r11d, DWORD PTR [rcx+324]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, -1035236496
	add r10d, DWORD PTR [rcx+328]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, -949202525
	add r9d, DWORD PTR [rcx+332]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	vpalignr ymm4, ymm0, ymm3, 4
	vpalignr ymm7, ymm2, ymm1, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm3, ymm3, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm2, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm3, ymm3, ymm6
	vpshufd ymm7, ymm3, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm3, ymm3, ymm6
	vmovdqu YMMWORD PTR [rcx+480], ymm3
	add r8d, -778901479
	add r8d, DWORD PTR [rcx+352]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, -694614492
	add ebp, DWORD PTR [rcx+356]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -200395387
	add ebx, DWORD PTR [rcx+360]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, 275423344
	add eax, DWORD PTR [rcx+364]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, 430227734
	add r12d, DWORD PTR [rcx+384]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 506948616
	add r11d, DWORD PTR [rcx+388]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, 659060556
	add r10d, DWORD PTR [rcx+392]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, 883997877
	add r9d, DWORD PTR [rcx+396]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, 958139571
	add r8d, DWORD PTR [rcx+416]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, 1322822218
	add ebp, DWORD PTR [rcx+420]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, 1537002063
	add ebx, DWORD PTR [rcx+424]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, 1747873779
	add eax, DWORD PTR [rcx+428]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, 1955562222
	add r12d, DWORD PTR [rcx+448]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 2024104815
	add r11d, DWORD PTR [rcx+452]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, -2067236844
	add r10d, DWORD PTR [rcx+456]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, -1933114872
	add r9d, DWORD PTR [rcx+460]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, -1866530822
	add r8d, DWORD PTR [rcx+480]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, -1538233109
	add ebp, DWORD PTR [rcx+484]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -1090935817
	add ebx, DWORD PTR [rcx+488]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, -965641998
	add eax, DWORD PTR [rcx+492]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add eax, DWORD PTR [rdi]
	add ebx, DWORD PTR [rdi+4]
	add ebp, DWORD PTR [rdi+8]
	add r8d, DWORD PTR [rdi+12]
	add r9d, DWORD PTR [rdi+16]
	add r10d, DWORD PTR [rdi+20]
	add r11d, DWORD PTR [rdi+24]
	add r12d, DWORD PTR [rdi+28]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+4], ebx
	mov DWORD PTR [rdi+8], ebp
	mov DWORD PTR [rdi+12], r8d
	mov DWORD PTR [rdi+16], r9d
	mov DWORD PTR [rdi+20], r10d
	mov DWORD PTR [rdi+24], r11d
	mov DWORD PTR [rdi+28], r12d
	cmp rdx, 1
	je 25f
	mov r13d, ebx
	xor r13d, ebp
	add r12d, 1116352408
	add r12d, DWORD PTR [rcx+16]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 1899447441
	add r11d, DWORD PTR [rcx+20]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, -1245643825
	add r10d, DWORD PTR [rcx+24]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, -373957723
	add r9d, DWORD PTR [rcx+28]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, 961987163
	add r8d, DWORD PTR [rcx+48]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, 1508970993
	add ebp, DWORD PTR [rcx+52]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -1841331548
	add ebx, DWORD PTR [rcx+56]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, -1424204075
	add eax, DWORD PTR [rcx+60]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, -670586216
	add r12d, DWORD PTR [rcx+80]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 310598401
	add r11d, DWORD PTR [rcx+84]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, 607225278
	add r10d, DWORD PTR [rcx+88]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, 1426881987
	add r9d, DWORD PTR [rcx+92]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, 1925078388
	add r8d, DWORD PTR [rcx+112]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, -2132889090
	add ebp, DWORD PTR [rcx+116]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -1680079193
	add ebx, DWORD PTR [rcx+120]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, -1046744716
	add eax, DWORD PTR [rcx+124]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, -459576895
	add r12d, DWORD PTR [rcx+144]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, -272742522
	add r11d, DWORD PTR [rcx+148]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, 264347078
	add r10d, DWORD PTR [rcx+152]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, 604807628
	add r9d, DWORD PTR [rcx+156]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, 770255983
	add r8d, DWORD PTR [rcx+176]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, 1249150122
	add ebp, DWORD PTR [rcx+180]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, 1555081692
	add ebx, DWORD PTR [rcx+184]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, 1996064986
	add eax, DWORD PTR [rcx+188]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, -1740746414
	add r12d, DWORD PTR [rcx+208]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, -1473132947
	add r11d, DWORD PTR [rcx+212]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, -1341970488
	add r10d, DWORD PTR [rcx+216]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, -1084653625
	add r9d, DWORD PTR [rcx+220]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, -958395405
	add r8d, DWORD PTR [rcx+240]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, -710438585
	add ebp, DWORD PTR [rcx+244]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, 113926993
	add ebx, DWORD PTR [rcx+248]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, 338241895
	add eax, DWORD PTR [rcx+252]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, 666307205
	add r12d, DWORD PTR [rcx+272]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 773529912
	add r11d, DWORD PTR [rcx+276]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, 1294757372
	add r10d, DWORD PTR [rcx+280]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, 1396182291
	add r9d, DWORD PTR [rcx+284]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, 1695183700
	add r8d, DWORD PTR [rcx+304]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, 1986661051
	add ebp, DWORD PTR [rcx+308]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -2117940946
	add ebx, DWORD PTR [rcx+312]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, -1838011259
	add eax, DWORD PTR [rcx+316]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, -1564481375
	add r12d, DWORD PTR [rcx+336]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, -1474664885
	add r11d, DWORD PTR [rcx+340]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, -1035236496
	add r10d, DWORD PTR [rcx+344]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, -949202525
	add r9d, DWORD PTR [rcx+348]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, -778901479
	add r8d, DWORD PTR [rcx+368]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, -694614492
	add ebp, DWORD PTR [rcx+372]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -200395387
	add ebx, DWORD PTR [rcx+376]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, 275423344
	add eax, DWORD PTR [rcx+380]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, 430227734
	add r12d, DWORD PTR [rcx+400]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 506948616
	add r11d, DWORD PTR [rcx+404]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, 659060556
	add r10d, DWORD PTR [rcx+408]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, 883997877
	add r9d, DWORD PTR [rcx+412]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, 958139571
	add r8d, DWORD PTR [rcx+432]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, 1322822218
	add ebp, DWORD PTR [rcx+436]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, 1537002063
	add ebx, DWORD PTR [rcx+440]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, 1747873779
	add eax, DWORD PTR [rcx+444]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, 1955562222
	add r12d, DWORD PTR [rcx+464]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 2024104815
	add r11d, DWORD PTR [rcx+468]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, -2067236844
	add r10d, DWORD PTR [rcx+472]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, -1933114872
	add r9d, DWORD PTR [rcx+476]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, -1866530822
	add r8d, DWORD PTR [rcx+496]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, -1538233109
	add ebp, DWORD PTR [rcx+500]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -1090935817
	add ebx, DWORD PTR [rcx+504]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, -965641998
	add eax, DWORD PTR [rcx+508]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add eax, DWORD PTR [rdi]
	add ebx, DWORD PTR [rdi+4]
	add ebp, DWORD PTR [rdi+8]
	add r8d, DWORD PTR [rdi+12]
	add r9d, DWORD PTR [rdi+16]
	add r10d, DWORD PTR [rdi+20]
	add r11d, DWORD PTR [rdi+24]
	add r12d, DWORD PTR [rdi+28]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+4], ebx
	mov DWORD PTR [rdi+8], ebp
	mov DWORD PTR [rdi+12], r8d
	mov DWORD PTR [rdi+16], r9d
	mov DWORD PTR [rdi+20], r10d
	mov DWORD PTR [rdi+24], r11d
	mov DWORD PTR [rdi+28], r12d
	add rsi, 128
	sub rdx, 2
	jmp 26f
25:
	add rsi, 64
	sub rdx, 1
26:
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [rcx+512]
	mov rbp, QWORD PTR [rcx+520]
	mov r12, QWORD PTR [rcx+528]
	mov r13, QWORD PTR [rcx+536]
	mov r14, QWORD PTR [rcx+544]
	mov r15, QWORD PTR [rcx+552]
	vzeroupper
	ret
	.p2align 6

vg_sha224_finalize:
	lea rsp, [rsp-616]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+560], rbx
	mov QWORD PTR [rcx+568], rbp
	mov QWORD PTR [rcx+576], r12
	mov QWORD PTR [rcx+584], r13
	mov QWORD PTR [rcx+592], r14
	mov QWORD PTR [rcx+600], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 63
	mov r9d, 128
	mov r14d, 0
	cmp r13, 56
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	mov eax, 64
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 56
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+32], r9
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 29b
	jmp 28f
27:
28:
	test rax, rax
	je 210f
212:
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	sub rax, 1
	jne 212b
	jmp 211f
210:
211:
	test r14, r14
	je 213f
	jmp 214f
213:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 48
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+32], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 48
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+80], xmm0
24:
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
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
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	lea rsp, [rsp+616]
	ret
	.p2align 6

vg_sha224_digest:
	lea rsp, [rsp-728]
	mov rcx, rsp
	add rcx, 8
	add rcx, 96
	mov QWORD PTR [rcx+560], rbx
	mov QWORD PTR [rcx+568], rbp
	mov QWORD PTR [rcx+576], r12
	mov QWORD PTR [rcx+584], r13
	mov QWORD PTR [rcx+592], r14
	mov QWORD PTR [rcx+600], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 96
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, 3926247204440088280
	movq xmm0, rax
	movabs rax, -644479594506691305
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	movabs rax, 7518782744944446257
	movq xmm0, rax
	movabs rax, -4685344894838272089
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi+16], xmm0
	mov r14, r12
	shr r14, 6
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 6
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov r10, r12
	and r10, 63
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
	add r13, 16
	add r11, 16
	sub r9, 1
	jne 24b
	jmp 23f
22:
23:
	mov rax, r10
	and rax, 15
	je 25f
	cmp r12, 8
	jb 27f
	cmp rax, 8
	jb 29f
	mov r8, QWORD PTR [r13]
	mov r9, QWORD PTR [r13+rax*1-8]
	mov ecx, 15
	sub rcx, rax
	shl rcx, 3
	shr r9, cl
	shr r9, 8
	mov rcx, rax
	sub rcx, 8
	shl rcx, 3
	mov edx, 128
	shl rdx, cl
	or r9, rdx
	movq xmm1, r8
	movq xmm2, r9
	punpcklqdq xmm1, xmm2
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
	jmp 210f
29:
	mov r8, QWORD PTR [r13+rax*1-8]
	mov ecx, 8
	sub rcx, rax
	shl rcx, 3
	shr r8, cl
	mov rcx, rax
	shl rcx, 3
	mov r9d, 128
	shl r9, cl
	or r8, r9
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+32], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+32], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
26:
	cmp r10, 56
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
215:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	movdqu xmm0, XMMWORD PTR [rbx+80]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
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
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	lea rsp, [rsp+728]
	ret
	.p2align 6

vg_sha224_finalize_avx2:
	lea rsp, [rsp-616]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+560], rbx
	mov QWORD PTR [rcx+568], rbp
	mov QWORD PTR [rcx+576], r12
	mov QWORD PTR [rcx+584], r13
	mov QWORD PTR [rcx+592], r14
	mov QWORD PTR [rcx+600], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 63
	mov r9d, 128
	mov r14d, 0
	cmp r13, 56
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	mov eax, 64
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 56
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+32], r9
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 29b
	jmp 28f
27:
28:
	test rax, rax
	je 210f
212:
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	sub rax, 1
	jne 212b
	jmp 211f
210:
211:
	test r14, r14
	je 213f
	jmp 214f
213:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 48
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+32], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 48
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+80], xmm0
24:
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
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
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	lea rsp, [rsp+616]
	ret
	.p2align 6

vg_sha224_digest_avx2:
	lea rsp, [rsp-728]
	mov rcx, rsp
	add rcx, 8
	add rcx, 96
	mov QWORD PTR [rcx+560], rbx
	mov QWORD PTR [rcx+568], rbp
	mov QWORD PTR [rcx+576], r12
	mov QWORD PTR [rcx+584], r13
	mov QWORD PTR [rcx+592], r14
	mov QWORD PTR [rcx+600], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 96
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, 3926247204440088280
	movq xmm0, rax
	movabs rax, -644479594506691305
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	movabs rax, 7518782744944446257
	movq xmm0, rax
	movabs rax, -4685344894838272089
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi+16], xmm0
	mov r14, r12
	shr r14, 6
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 6
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov r10, r12
	and r10, 63
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
	add r13, 16
	add r11, 16
	sub r9, 1
	jne 24b
	jmp 23f
22:
23:
	mov rax, r10
	and rax, 15
	je 25f
	cmp r12, 8
	jb 27f
	cmp rax, 8
	jb 29f
	mov r8, QWORD PTR [r13]
	mov r9, QWORD PTR [r13+rax*1-8]
	mov ecx, 15
	sub rcx, rax
	shl rcx, 3
	shr r9, cl
	shr r9, 8
	mov rcx, rax
	sub rcx, 8
	shl rcx, 3
	mov edx, 128
	shl rdx, cl
	or r9, rdx
	movq xmm1, r8
	movq xmm2, r9
	punpcklqdq xmm1, xmm2
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
	jmp 210f
29:
	mov r8, QWORD PTR [r13+rax*1-8]
	mov ecx, 8
	sub rcx, rax
	shl rcx, 3
	shr r8, cl
	mov rcx, rax
	shl rcx, 3
	mov r9d, 128
	shl r9, cl
	or r8, r9
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+32], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+32], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
26:
	cmp r10, 56
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
215:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	movdqu xmm0, XMMWORD PTR [rbx+80]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
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
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	lea rsp, [rsp+728]
	ret
	.p2align 6

vg_sha224_finalize_shani:
	lea rsp, [rsp-616]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+560], rbx
	mov QWORD PTR [rcx+568], rbp
	mov QWORD PTR [rcx+576], r12
	mov QWORD PTR [rcx+584], r13
	mov QWORD PTR [rcx+592], r14
	mov QWORD PTR [rcx+600], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 63
	mov r9d, 128
	mov r14d, 0
	cmp r13, 56
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	mov eax, 64
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 56
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+32], r9
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 29b
	jmp 28f
27:
28:
	test rax, rax
	je 210f
212:
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	sub rax, 1
	jne 212b
	jmp 211f
210:
211:
	test r14, r14
	je 213f
	jmp 214f
213:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 48
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+32], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 48
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+80], xmm0
24:
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
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
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	lea rsp, [rsp+616]
	ret
	.p2align 6

vg_sha224_digest_shani:
	lea rsp, [rsp-728]
	mov rcx, rsp
	add rcx, 8
	add rcx, 96
	mov QWORD PTR [rcx+560], rbx
	mov QWORD PTR [rcx+568], rbp
	mov QWORD PTR [rcx+576], r12
	mov QWORD PTR [rcx+584], r13
	mov QWORD PTR [rcx+592], r14
	mov QWORD PTR [rcx+600], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 96
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, 3926247204440088280
	movq xmm0, rax
	movabs rax, -644479594506691305
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	movabs rax, 7518782744944446257
	movq xmm0, rax
	movabs rax, -4685344894838272089
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi+16], xmm0
	mov r14, r12
	shr r14, 6
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 6
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov r10, r12
	and r10, 63
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
	add r13, 16
	add r11, 16
	sub r9, 1
	jne 24b
	jmp 23f
22:
23:
	mov rax, r10
	and rax, 15
	je 25f
	cmp r12, 8
	jb 27f
	cmp rax, 8
	jb 29f
	mov r8, QWORD PTR [r13]
	mov r9, QWORD PTR [r13+rax*1-8]
	mov ecx, 15
	sub rcx, rax
	shl rcx, 3
	shr r9, cl
	shr r9, 8
	mov rcx, rax
	sub rcx, 8
	shl rcx, 3
	mov edx, 128
	shl rdx, cl
	or r9, rdx
	movq xmm1, r8
	movq xmm2, r9
	punpcklqdq xmm1, xmm2
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
	jmp 210f
29:
	mov r8, QWORD PTR [r13+rax*1-8]
	mov ecx, 8
	sub rcx, rax
	shl rcx, 3
	shr r8, cl
	mov rcx, rax
	shl rcx, 3
	mov r9d, 128
	shl r9, cl
	or r8, r9
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+32], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+32], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
26:
	cmp r10, 56
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
215:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	movdqu xmm0, XMMWORD PTR [rbx+80]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
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
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	lea rsp, [rsp+728]
	ret
	.p2align 6

vg_sha256_update:
	lea rsp, [rsp-616]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+560], rbx
	mov QWORD PTR [r8+568], rbp
	mov QWORD PTR [r8+576], r12
	mov QWORD PTR [r8+584], r13
	mov QWORD PTR [r8+592], r14
	mov QWORD PTR [r8+600], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 63
20:
	test r13, r13
	je 21f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 23f
	jmp 24f
23:
	mov rax, r12
24:
	sub r12, rax
	cmp rax, 8
	jb 25f
27:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+32], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 27b
	jmp 26f
25:
26:
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 64
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 32
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 64
	jae 213f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 215f
	jmp 216f
215:
	mov rax, r12
216:
	sub r12, rax
	cmp rax, 8
	jb 217f
219:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+32], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 219b
	jmp 218f
217:
218:
	test rax, rax
	je 220f
222:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 64
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 32
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 63
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 6
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	lea rsp, [rsp+616]
	ret
	.p2align 6

vg_sha256_finalize:
	lea rsp, [rsp-616]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+560], rbx
	mov QWORD PTR [rcx+568], rbp
	mov QWORD PTR [rcx+576], r12
	mov QWORD PTR [rcx+584], r13
	mov QWORD PTR [rcx+592], r14
	mov QWORD PTR [rcx+600], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 63
	mov r9d, 128
	mov r14d, 0
	cmp r13, 56
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	mov eax, 64
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 56
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+32], r9
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 29b
	jmp 28f
27:
28:
	test rax, rax
	je 210f
212:
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	sub rax, 1
	jne 212b
	jmp 211f
210:
211:
	test r14, r14
	je 213f
	jmp 214f
213:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 48
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+32], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 48
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+80], xmm0
24:
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
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
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	lea rsp, [rsp+616]
	ret
	.p2align 6

vg_sha256_update_scratch:
	mov QWORD PTR [r8+560], rbx
	mov QWORD PTR [r8+568], rbp
	mov QWORD PTR [r8+576], r12
	mov QWORD PTR [r8+584], r13
	mov QWORD PTR [r8+592], r14
	mov QWORD PTR [r8+600], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 63
20:
	test r13, r13
	je 21f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 23f
	jmp 24f
23:
	mov rax, r12
24:
	sub r12, rax
	cmp rax, 8
	jb 25f
27:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+32], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 27b
	jmp 26f
25:
26:
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 64
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 32
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 64
	jae 213f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 215f
	jmp 216f
215:
	mov rax, r12
216:
	sub r12, rax
	cmp rax, 8
	jb 217f
219:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+32], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 219b
	jmp 218f
217:
218:
	test rax, rax
	je 220f
222:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 64
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 32
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 63
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 6
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	ret
	.p2align 6

vg_sha256_finalize_scratch:
	mov QWORD PTR [rcx+560], rbx
	mov QWORD PTR [rcx+568], rbp
	mov QWORD PTR [rcx+576], r12
	mov QWORD PTR [rcx+584], r13
	mov QWORD PTR [rcx+592], r14
	mov QWORD PTR [rcx+600], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 63
	mov r9d, 128
	mov r14d, 0
	cmp r13, 56
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	mov eax, 64
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 56
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+32], r9
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 29b
	jmp 28f
27:
28:
	test rax, rax
	je 210f
212:
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	sub rax, 1
	jne 212b
	jmp 211f
210:
211:
	test r14, r14
	je 213f
	jmp 214f
213:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 48
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+32], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 48
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+80], xmm0
24:
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
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
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	ret
	.p2align 6

vg_sha256_digest:
	lea rsp, [rsp-728]
	mov rcx, rsp
	add rcx, 8
	add rcx, 96
	mov QWORD PTR [rcx+560], rbx
	mov QWORD PTR [rcx+568], rbp
	mov QWORD PTR [rcx+576], r12
	mov QWORD PTR [rcx+584], r13
	mov QWORD PTR [rcx+592], r14
	mov QWORD PTR [rcx+600], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 96
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, -4942790177982912921
	movq xmm0, rax
	movabs rax, -6534734903820487822
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	movabs rax, -7276294671082564993
	movq xmm0, rax
	movabs rax, 6620516960021240235
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi+16], xmm0
	mov r14, r12
	shr r14, 6
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 6
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov r10, r12
	and r10, 63
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
	add r13, 16
	add r11, 16
	sub r9, 1
	jne 24b
	jmp 23f
22:
23:
	mov rax, r10
	and rax, 15
	je 25f
	cmp r12, 8
	jb 27f
	cmp rax, 8
	jb 29f
	mov r8, QWORD PTR [r13]
	mov r9, QWORD PTR [r13+rax*1-8]
	mov ecx, 15
	sub rcx, rax
	shl rcx, 3
	shr r9, cl
	shr r9, 8
	mov rcx, rax
	sub rcx, 8
	shl rcx, 3
	mov edx, 128
	shl rdx, cl
	or r9, rdx
	movq xmm1, r8
	movq xmm2, r9
	punpcklqdq xmm1, xmm2
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
	jmp 210f
29:
	mov r8, QWORD PTR [r13+rax*1-8]
	mov ecx, 8
	sub rcx, rax
	shl rcx, 3
	shr r8, cl
	mov rcx, rax
	shl rcx, 3
	mov r9d, 128
	shl r9, cl
	or r8, r9
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+32], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+32], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
26:
	cmp r10, 56
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
215:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	movdqu xmm0, XMMWORD PTR [rbx+80]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
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
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	lea rsp, [rsp+728]
	ret
	.p2align 6

vg_sha256_update_avx2:
	lea rsp, [rsp-616]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+560], rbx
	mov QWORD PTR [r8+568], rbp
	mov QWORD PTR [r8+576], r12
	mov QWORD PTR [r8+584], r13
	mov QWORD PTR [r8+592], r14
	mov QWORD PTR [r8+600], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 63
20:
	test r13, r13
	je 21f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 23f
	jmp 24f
23:
	mov rax, r12
24:
	sub r12, rax
	cmp rax, 8
	jb 25f
27:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+32], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 27b
	jmp 26f
25:
26:
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 64
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 32
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 64
	jae 213f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 215f
	jmp 216f
215:
	mov rax, r12
216:
	sub r12, rax
	cmp rax, 8
	jb 217f
219:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+32], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 219b
	jmp 218f
217:
218:
	test rax, rax
	je 220f
222:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 64
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 32
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 63
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 6
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	lea rsp, [rsp+616]
	ret
	.p2align 6

vg_sha256_finalize_avx2:
	lea rsp, [rsp-616]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+560], rbx
	mov QWORD PTR [rcx+568], rbp
	mov QWORD PTR [rcx+576], r12
	mov QWORD PTR [rcx+584], r13
	mov QWORD PTR [rcx+592], r14
	mov QWORD PTR [rcx+600], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 63
	mov r9d, 128
	mov r14d, 0
	cmp r13, 56
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	mov eax, 64
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 56
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+32], r9
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 29b
	jmp 28f
27:
28:
	test rax, rax
	je 210f
212:
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	sub rax, 1
	jne 212b
	jmp 211f
210:
211:
	test r14, r14
	je 213f
	jmp 214f
213:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 48
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+32], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 48
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+80], xmm0
24:
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
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
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	lea rsp, [rsp+616]
	ret
	.p2align 6

vg_sha256_update_scratch_avx2:
	mov QWORD PTR [r8+560], rbx
	mov QWORD PTR [r8+568], rbp
	mov QWORD PTR [r8+576], r12
	mov QWORD PTR [r8+584], r13
	mov QWORD PTR [r8+592], r14
	mov QWORD PTR [r8+600], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 63
20:
	test r13, r13
	je 21f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 23f
	jmp 24f
23:
	mov rax, r12
24:
	sub r12, rax
	cmp rax, 8
	jb 25f
27:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+32], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 27b
	jmp 26f
25:
26:
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 64
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 32
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 64
	jae 213f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 215f
	jmp 216f
215:
	mov rax, r12
216:
	sub r12, rax
	cmp rax, 8
	jb 217f
219:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+32], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 219b
	jmp 218f
217:
218:
	test rax, rax
	je 220f
222:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 64
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 32
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 63
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 6
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	ret
	.p2align 6

vg_sha256_finalize_scratch_avx2:
	mov QWORD PTR [rcx+560], rbx
	mov QWORD PTR [rcx+568], rbp
	mov QWORD PTR [rcx+576], r12
	mov QWORD PTR [rcx+584], r13
	mov QWORD PTR [rcx+592], r14
	mov QWORD PTR [rcx+600], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 63
	mov r9d, 128
	mov r14d, 0
	cmp r13, 56
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	mov eax, 64
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 56
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+32], r9
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 29b
	jmp 28f
27:
28:
	test rax, rax
	je 210f
212:
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	sub rax, 1
	jne 212b
	jmp 211f
210:
211:
	test r14, r14
	je 213f
	jmp 214f
213:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 48
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+32], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 48
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+80], xmm0
24:
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
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
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	ret
	.p2align 6

vg_sha256_digest_avx2:
	lea rsp, [rsp-728]
	mov rcx, rsp
	add rcx, 8
	add rcx, 96
	mov QWORD PTR [rcx+560], rbx
	mov QWORD PTR [rcx+568], rbp
	mov QWORD PTR [rcx+576], r12
	mov QWORD PTR [rcx+584], r13
	mov QWORD PTR [rcx+592], r14
	mov QWORD PTR [rcx+600], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 96
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, -4942790177982912921
	movq xmm0, rax
	movabs rax, -6534734903820487822
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	movabs rax, -7276294671082564993
	movq xmm0, rax
	movabs rax, 6620516960021240235
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi+16], xmm0
	mov r14, r12
	shr r14, 6
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 6
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov r10, r12
	and r10, 63
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
	add r13, 16
	add r11, 16
	sub r9, 1
	jne 24b
	jmp 23f
22:
23:
	mov rax, r10
	and rax, 15
	je 25f
	cmp r12, 8
	jb 27f
	cmp rax, 8
	jb 29f
	mov r8, QWORD PTR [r13]
	mov r9, QWORD PTR [r13+rax*1-8]
	mov ecx, 15
	sub rcx, rax
	shl rcx, 3
	shr r9, cl
	shr r9, 8
	mov rcx, rax
	sub rcx, 8
	shl rcx, 3
	mov edx, 128
	shl rdx, cl
	or r9, rdx
	movq xmm1, r8
	movq xmm2, r9
	punpcklqdq xmm1, xmm2
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
	jmp 210f
29:
	mov r8, QWORD PTR [r13+rax*1-8]
	mov ecx, 8
	sub rcx, rax
	shl rcx, 3
	shr r8, cl
	mov rcx, rax
	shl rcx, 3
	mov r9d, 128
	shl r9, cl
	or r8, r9
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+32], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+32], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
26:
	cmp r10, 56
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
215:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	movdqu xmm0, XMMWORD PTR [rbx+80]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
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
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	lea rsp, [rsp+728]
	ret
	.p2align 6

vg_sha256_update_shani:
	lea rsp, [rsp-616]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+560], rbx
	mov QWORD PTR [r8+568], rbp
	mov QWORD PTR [r8+576], r12
	mov QWORD PTR [r8+584], r13
	mov QWORD PTR [r8+592], r14
	mov QWORD PTR [r8+600], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 63
20:
	test r13, r13
	je 21f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 23f
	jmp 24f
23:
	mov rax, r12
24:
	sub r12, rax
	cmp rax, 8
	jb 25f
27:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+32], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 27b
	jmp 26f
25:
26:
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 64
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 32
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 64
	jae 213f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 215f
	jmp 216f
215:
	mov rax, r12
216:
	sub r12, rax
	cmp rax, 8
	jb 217f
219:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+32], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 219b
	jmp 218f
217:
218:
	test rax, rax
	je 220f
222:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 64
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 32
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 63
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 6
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	lea rsp, [rsp+616]
	ret
	.p2align 6

vg_sha256_finalize_shani:
	lea rsp, [rsp-616]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+560], rbx
	mov QWORD PTR [rcx+568], rbp
	mov QWORD PTR [rcx+576], r12
	mov QWORD PTR [rcx+584], r13
	mov QWORD PTR [rcx+592], r14
	mov QWORD PTR [rcx+600], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 63
	mov r9d, 128
	mov r14d, 0
	cmp r13, 56
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	mov eax, 64
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 56
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+32], r9
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 29b
	jmp 28f
27:
28:
	test rax, rax
	je 210f
212:
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	sub rax, 1
	jne 212b
	jmp 211f
210:
211:
	test r14, r14
	je 213f
	jmp 214f
213:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 48
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+32], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 48
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+80], xmm0
24:
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
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
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	lea rsp, [rsp+616]
	ret
	.p2align 6

vg_sha256_update_scratch_shani:
	mov QWORD PTR [r8+560], rbx
	mov QWORD PTR [r8+568], rbp
	mov QWORD PTR [r8+576], r12
	mov QWORD PTR [r8+584], r13
	mov QWORD PTR [r8+592], r14
	mov QWORD PTR [r8+600], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 63
20:
	test r13, r13
	je 21f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 23f
	jmp 24f
23:
	mov rax, r12
24:
	sub r12, rax
	cmp rax, 8
	jb 25f
27:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+32], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 27b
	jmp 26f
25:
26:
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 64
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 32
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 64
	jae 213f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 215f
	jmp 216f
215:
	mov rax, r12
216:
	sub r12, rax
	cmp rax, 8
	jb 217f
219:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+32], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 219b
	jmp 218f
217:
218:
	test rax, rax
	je 220f
222:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 64
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 32
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 63
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 6
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	ret
	.p2align 6

vg_sha256_finalize_scratch_shani:
	mov QWORD PTR [rcx+560], rbx
	mov QWORD PTR [rcx+568], rbp
	mov QWORD PTR [rcx+576], r12
	mov QWORD PTR [rcx+584], r13
	mov QWORD PTR [rcx+592], r14
	mov QWORD PTR [rcx+600], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 63
	mov r9d, 128
	mov r14d, 0
	cmp r13, 56
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	mov eax, 64
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 56
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+32], r9
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 29b
	jmp 28f
27:
28:
	test rax, rax
	je 210f
212:
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	sub rax, 1
	jne 212b
	jmp 211f
210:
211:
	test r14, r14
	je 213f
	jmp 214f
213:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 48
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+32], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 48
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+80], xmm0
24:
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
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
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	ret
	.p2align 6

vg_sha256_digest_shani:
	lea rsp, [rsp-728]
	mov rcx, rsp
	add rcx, 8
	add rcx, 96
	mov QWORD PTR [rcx+560], rbx
	mov QWORD PTR [rcx+568], rbp
	mov QWORD PTR [rcx+576], r12
	mov QWORD PTR [rcx+584], r13
	mov QWORD PTR [rcx+592], r14
	mov QWORD PTR [rcx+600], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 96
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, -4942790177982912921
	movq xmm0, rax
	movabs rax, -6534734903820487822
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	movabs rax, -7276294671082564993
	movq xmm0, rax
	movabs rax, 6620516960021240235
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi+16], xmm0
	mov r14, r12
	shr r14, 6
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 6
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov r10, r12
	and r10, 63
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
	add r13, 16
	add r11, 16
	sub r9, 1
	jne 24b
	jmp 23f
22:
23:
	mov rax, r10
	and rax, 15
	je 25f
	cmp r12, 8
	jb 27f
	cmp rax, 8
	jb 29f
	mov r8, QWORD PTR [r13]
	mov r9, QWORD PTR [r13+rax*1-8]
	mov ecx, 15
	sub rcx, rax
	shl rcx, 3
	shr r9, cl
	shr r9, 8
	mov rcx, rax
	sub rcx, 8
	shl rcx, 3
	mov edx, 128
	shl rdx, cl
	or r9, rdx
	movq xmm1, r8
	movq xmm2, r9
	punpcklqdq xmm1, xmm2
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
	jmp 210f
29:
	mov r8, QWORD PTR [r13+rax*1-8]
	mov ecx, 8
	sub rcx, rax
	shl rcx, 3
	shr r8, cl
	mov rcx, rax
	shl rcx, 3
	mov r9d, 128
	shl r9, cl
	or r8, r9
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+32], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+32], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+32], xmm1
26:
	cmp r10, 56
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
215:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	movdqu xmm0, XMMWORD PTR [rbx+80]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
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
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	lea rsp, [rsp+728]
	ret
	.p2align 6
