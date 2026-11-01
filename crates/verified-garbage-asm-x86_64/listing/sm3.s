// The functions of `src/sm3.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm3_compress:
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
	mov r13d, DWORD PTR [rsi+4]
	bswap r13d
	mov DWORD PTR [rcx+4], r13d
	mov r13d, DWORD PTR [rsi+8]
	bswap r13d
	mov DWORD PTR [rcx+8], r13d
	mov r13d, DWORD PTR [rsi+12]
	bswap r13d
	mov DWORD PTR [rcx+12], r13d
	mov r13d, DWORD PTR [rsi+16]
	bswap r13d
	mov DWORD PTR [rcx+16], r13d
	mov r13d, eax
	ror r13d, 20
	mov r14d, r13d
	add r14d, r9d
	add r14d, 2043430169
	ror r14d, 25
	add r12d, r14d
	xor r13d, r14d
	add r8d, r13d
	add r12d, DWORD PTR [rcx]
	mov r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+16]
	add r8d, r13d
	mov r13d, eax
	xor r13d, ebx
	xor r13d, ebp
	add r8d, r13d
	mov r13d, r9d
	xor r13d, r10d
	xor r13d, r11d
	add r12d, r13d
	ror ebx, 23
	ror r10d, 13
	mov r13d, r12d
	ror r13d, 23
	mov r14d, r12d
	ror r14d, 15
	xor r12d, r13d
	xor r12d, r14d
	mov r13d, DWORD PTR [rsi+20]
	bswap r13d
	mov DWORD PTR [rcx+20], r13d
	mov r13d, r8d
	ror r13d, 20
	mov r14d, r13d
	add r14d, r12d
	add r14d, -208106958
	ror r14d, 25
	add r11d, r14d
	xor r13d, r14d
	add ebp, r13d
	add r11d, DWORD PTR [rcx+4]
	mov r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+20]
	add ebp, r13d
	mov r13d, r8d
	xor r13d, eax
	xor r13d, ebx
	add ebp, r13d
	mov r13d, r12d
	xor r13d, r9d
	xor r13d, r10d
	add r11d, r13d
	ror eax, 23
	ror r9d, 13
	mov r13d, r11d
	ror r13d, 23
	mov r14d, r11d
	ror r14d, 15
	xor r11d, r13d
	xor r11d, r14d
	mov r13d, DWORD PTR [rsi+24]
	bswap r13d
	mov DWORD PTR [rcx+24], r13d
	mov r13d, ebp
	ror r13d, 20
	mov r14d, r13d
	add r14d, r11d
	add r14d, -416213915
	ror r14d, 25
	add r10d, r14d
	xor r13d, r14d
	add ebx, r13d
	add r10d, DWORD PTR [rcx+8]
	mov r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx+24]
	add ebx, r13d
	mov r13d, ebp
	xor r13d, r8d
	xor r13d, eax
	add ebx, r13d
	mov r13d, r11d
	xor r13d, r12d
	xor r13d, r9d
	add r10d, r13d
	ror r8d, 23
	ror r12d, 13
	mov r13d, r10d
	ror r13d, 23
	mov r14d, r10d
	ror r14d, 15
	xor r10d, r13d
	xor r10d, r14d
	mov r13d, DWORD PTR [rsi+28]
	bswap r13d
	mov DWORD PTR [rcx+28], r13d
	mov r13d, ebx
	ror r13d, 20
	mov r14d, r13d
	add r14d, r10d
	add r14d, -832427829
	ror r14d, 25
	add r9d, r14d
	xor r13d, r14d
	add eax, r13d
	add r9d, DWORD PTR [rcx+12]
	mov r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+28]
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	xor r13d, r8d
	add eax, r13d
	mov r13d, r10d
	xor r13d, r11d
	xor r13d, r12d
	add r9d, r13d
	ror ebp, 23
	ror r11d, 13
	mov r13d, r9d
	ror r13d, 23
	mov r14d, r9d
	ror r14d, 15
	xor r9d, r13d
	xor r9d, r14d
	mov r13d, DWORD PTR [rsi+32]
	bswap r13d
	mov DWORD PTR [rcx+32], r13d
	mov r13d, eax
	ror r13d, 20
	mov r14d, r13d
	add r14d, r9d
	add r14d, -1664855657
	ror r14d, 25
	add r12d, r14d
	xor r13d, r14d
	add r8d, r13d
	add r12d, DWORD PTR [rcx+16]
	mov r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+32]
	add r8d, r13d
	mov r13d, eax
	xor r13d, ebx
	xor r13d, ebp
	add r8d, r13d
	mov r13d, r9d
	xor r13d, r10d
	xor r13d, r11d
	add r12d, r13d
	ror ebx, 23
	ror r10d, 13
	mov r13d, r12d
	ror r13d, 23
	mov r14d, r12d
	ror r14d, 15
	xor r12d, r13d
	xor r12d, r14d
	mov r13d, DWORD PTR [rsi+36]
	bswap r13d
	mov DWORD PTR [rcx+36], r13d
	mov r13d, r8d
	ror r13d, 20
	mov r14d, r13d
	add r14d, r12d
	add r14d, 965255983
	ror r14d, 25
	add r11d, r14d
	xor r13d, r14d
	add ebp, r13d
	add r11d, DWORD PTR [rcx+20]
	mov r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx+36]
	add ebp, r13d
	mov r13d, r8d
	xor r13d, eax
	xor r13d, ebx
	add ebp, r13d
	mov r13d, r12d
	xor r13d, r9d
	xor r13d, r10d
	add r11d, r13d
	ror eax, 23
	ror r9d, 13
	mov r13d, r11d
	ror r13d, 23
	mov r14d, r11d
	ror r14d, 15
	xor r11d, r13d
	xor r11d, r14d
	mov r13d, DWORD PTR [rsi+40]
	bswap r13d
	mov DWORD PTR [rcx+40], r13d
	mov r13d, ebp
	ror r13d, 20
	mov r14d, r13d
	add r14d, r11d
	add r14d, 1930511966
	ror r14d, 25
	add r10d, r14d
	xor r13d, r14d
	add ebx, r13d
	add r10d, DWORD PTR [rcx+24]
	mov r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx+40]
	add ebx, r13d
	mov r13d, ebp
	xor r13d, r8d
	xor r13d, eax
	add ebx, r13d
	mov r13d, r11d
	xor r13d, r12d
	xor r13d, r9d
	add r10d, r13d
	ror r8d, 23
	ror r12d, 13
	mov r13d, r10d
	ror r13d, 23
	mov r14d, r10d
	ror r14d, 15
	xor r10d, r13d
	xor r10d, r14d
	mov r13d, DWORD PTR [rsi+44]
	bswap r13d
	mov DWORD PTR [rcx+44], r13d
	mov r13d, ebx
	ror r13d, 20
	mov r14d, r13d
	add r14d, r10d
	add r14d, -433943364
	ror r14d, 25
	add r9d, r14d
	xor r13d, r14d
	add eax, r13d
	add r9d, DWORD PTR [rcx+28]
	mov r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+44]
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	xor r13d, r8d
	add eax, r13d
	mov r13d, r10d
	xor r13d, r11d
	xor r13d, r12d
	add r9d, r13d
	ror ebp, 23
	ror r11d, 13
	mov r13d, r9d
	ror r13d, 23
	mov r14d, r9d
	ror r14d, 15
	xor r9d, r13d
	xor r9d, r14d
	mov r13d, DWORD PTR [rsi+48]
	bswap r13d
	mov DWORD PTR [rcx+48], r13d
	mov r13d, eax
	ror r13d, 20
	mov r14d, r13d
	add r14d, r9d
	add r14d, -867886727
	ror r14d, 25
	add r12d, r14d
	xor r13d, r14d
	add r8d, r13d
	add r12d, DWORD PTR [rcx+32]
	mov r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+48]
	add r8d, r13d
	mov r13d, eax
	xor r13d, ebx
	xor r13d, ebp
	add r8d, r13d
	mov r13d, r9d
	xor r13d, r10d
	xor r13d, r11d
	add r12d, r13d
	ror ebx, 23
	ror r10d, 13
	mov r13d, r12d
	ror r13d, 23
	mov r14d, r12d
	ror r14d, 15
	xor r12d, r13d
	xor r12d, r14d
	mov r13d, DWORD PTR [rsi+52]
	bswap r13d
	mov DWORD PTR [rcx+52], r13d
	mov r13d, r8d
	ror r13d, 20
	mov r14d, r13d
	add r14d, r12d
	add r14d, -1735773453
	ror r14d, 25
	add r11d, r14d
	xor r13d, r14d
	add ebp, r13d
	add r11d, DWORD PTR [rcx+36]
	mov r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx+52]
	add ebp, r13d
	mov r13d, r8d
	xor r13d, eax
	xor r13d, ebx
	add ebp, r13d
	mov r13d, r12d
	xor r13d, r9d
	xor r13d, r10d
	add r11d, r13d
	ror eax, 23
	ror r9d, 13
	mov r13d, r11d
	ror r13d, 23
	mov r14d, r11d
	ror r14d, 15
	xor r11d, r13d
	xor r11d, r14d
	mov r13d, DWORD PTR [rsi+56]
	bswap r13d
	mov DWORD PTR [rcx+56], r13d
	mov r13d, ebp
	ror r13d, 20
	mov r14d, r13d
	add r14d, r11d
	add r14d, 823420391
	ror r14d, 25
	add r10d, r14d
	xor r13d, r14d
	add ebx, r13d
	add r10d, DWORD PTR [rcx+40]
	mov r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+56]
	add ebx, r13d
	mov r13d, ebp
	xor r13d, r8d
	xor r13d, eax
	add ebx, r13d
	mov r13d, r11d
	xor r13d, r12d
	xor r13d, r9d
	add r10d, r13d
	ror r8d, 23
	ror r12d, 13
	mov r13d, r10d
	ror r13d, 23
	mov r14d, r10d
	ror r14d, 15
	xor r10d, r13d
	xor r10d, r14d
	mov r13d, DWORD PTR [rsi+60]
	bswap r13d
	mov DWORD PTR [rcx+60], r13d
	mov r13d, ebx
	ror r13d, 20
	mov r14d, r13d
	add r14d, r10d
	add r14d, 1646840782
	ror r14d, 25
	add r9d, r14d
	xor r13d, r14d
	add eax, r13d
	add r9d, DWORD PTR [rcx+44]
	mov r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+60]
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	xor r13d, r8d
	add eax, r13d
	mov r13d, r10d
	xor r13d, r11d
	xor r13d, r12d
	add r9d, r13d
	ror ebp, 23
	ror r11d, 13
	mov r13d, r9d
	ror r13d, 23
	mov r14d, r9d
	ror r14d, 15
	xor r9d, r13d
	xor r9d, r14d
	mov r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+28]
	mov r14d, DWORD PTR [rcx+52]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+12]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+40]
	mov DWORD PTR [rcx], r13d
	mov r13d, eax
	ror r13d, 20
	mov r14d, r13d
	add r14d, r9d
	add r14d, -1001285732
	ror r14d, 25
	add r12d, r14d
	xor r13d, r14d
	add r8d, r13d
	add r12d, DWORD PTR [rcx+48]
	mov r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx]
	add r8d, r13d
	mov r13d, eax
	xor r13d, ebx
	xor r13d, ebp
	add r8d, r13d
	mov r13d, r9d
	xor r13d, r10d
	xor r13d, r11d
	add r12d, r13d
	ror ebx, 23
	ror r10d, 13
	mov r13d, r12d
	ror r13d, 23
	mov r14d, r12d
	ror r14d, 15
	xor r12d, r13d
	xor r12d, r14d
	mov r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+32]
	mov r14d, DWORD PTR [rcx+56]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+16]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+44]
	mov DWORD PTR [rcx+4], r13d
	mov r13d, r8d
	ror r13d, 20
	mov r14d, r13d
	add r14d, r12d
	add r14d, -2002571463
	ror r14d, 25
	add r11d, r14d
	xor r13d, r14d
	add ebp, r13d
	add r11d, DWORD PTR [rcx+52]
	mov r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+4]
	add ebp, r13d
	mov r13d, r8d
	xor r13d, eax
	xor r13d, ebx
	add ebp, r13d
	mov r13d, r12d
	xor r13d, r9d
	xor r13d, r10d
	add r11d, r13d
	ror eax, 23
	ror r9d, 13
	mov r13d, r11d
	ror r13d, 23
	mov r14d, r11d
	ror r14d, 15
	xor r11d, r13d
	xor r11d, r14d
	mov r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx+36]
	mov r14d, DWORD PTR [rcx+60]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+20]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+48]
	mov DWORD PTR [rcx+8], r13d
	mov r13d, ebp
	ror r13d, 20
	mov r14d, r13d
	add r14d, r11d
	add r14d, 289824371
	ror r14d, 25
	add r10d, r14d
	xor r13d, r14d
	add ebx, r13d
	add r10d, DWORD PTR [rcx+56]
	mov r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+8]
	add ebx, r13d
	mov r13d, ebp
	xor r13d, r8d
	xor r13d, eax
	add ebx, r13d
	mov r13d, r11d
	xor r13d, r12d
	xor r13d, r9d
	add r10d, r13d
	ror r8d, 23
	ror r12d, 13
	mov r13d, r10d
	ror r13d, 23
	mov r14d, r10d
	ror r14d, 15
	xor r10d, r13d
	xor r10d, r14d
	mov r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+40]
	mov r14d, DWORD PTR [rcx]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+24]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+52]
	mov DWORD PTR [rcx+12], r13d
	mov r13d, ebx
	ror r13d, 20
	mov r14d, r13d
	add r14d, r10d
	add r14d, 579648742
	ror r14d, 25
	add r9d, r14d
	xor r13d, r14d
	add eax, r13d
	add r9d, DWORD PTR [rcx+60]
	mov r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+12]
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	xor r13d, r8d
	add eax, r13d
	mov r13d, r10d
	xor r13d, r11d
	xor r13d, r12d
	add r9d, r13d
	ror ebp, 23
	ror r11d, 13
	mov r13d, r9d
	ror r13d, 23
	mov r14d, r9d
	ror r14d, 15
	xor r9d, r13d
	xor r9d, r14d
	mov r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+44]
	mov r14d, DWORD PTR [rcx+4]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+28]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+56]
	mov DWORD PTR [rcx+16], r13d
	mov r13d, eax
	ror r13d, 20
	mov r14d, r13d
	add r14d, r9d
	add r14d, -1651869049
	ror r14d, 25
	add r12d, r14d
	xor r13d, r14d
	add r8d, r13d
	add r12d, DWORD PTR [rcx]
	mov r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+16]
	add r8d, r13d
	mov r13d, eax
	or r13d, ebx
	and r13d, ebp
	mov r14d, eax
	and r14d, ebx
	or r13d, r14d
	add r8d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r13d, r9d
	xor r13d, r11d
	add r12d, r13d
	ror ebx, 23
	ror r10d, 13
	mov r13d, r12d
	ror r13d, 23
	mov r14d, r12d
	ror r14d, 15
	xor r12d, r13d
	xor r12d, r14d
	mov r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx+48]
	mov r14d, DWORD PTR [rcx+8]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+32]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+60]
	mov DWORD PTR [rcx+20], r13d
	mov r13d, r8d
	ror r13d, 20
	mov r14d, r13d
	add r14d, r12d
	add r14d, 991229199
	ror r14d, 25
	add r11d, r14d
	xor r13d, r14d
	add ebp, r13d
	add r11d, DWORD PTR [rcx+4]
	mov r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+20]
	add ebp, r13d
	mov r13d, r8d
	or r13d, eax
	and r13d, ebx
	mov r14d, r8d
	and r14d, eax
	or r13d, r14d
	add ebp, r13d
	mov r13d, r9d
	xor r13d, r10d
	and r13d, r12d
	xor r13d, r10d
	add r11d, r13d
	ror eax, 23
	ror r9d, 13
	mov r13d, r11d
	ror r13d, 23
	mov r14d, r11d
	ror r14d, 15
	xor r11d, r13d
	xor r11d, r14d
	mov r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx+52]
	mov r14d, DWORD PTR [rcx+12]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+36]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx]
	mov DWORD PTR [rcx+24], r13d
	mov r13d, ebp
	ror r13d, 20
	mov r14d, r13d
	add r14d, r11d
	add r14d, 1982458398
	ror r14d, 25
	add r10d, r14d
	xor r13d, r14d
	add ebx, r13d
	add r10d, DWORD PTR [rcx+8]
	mov r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx+24]
	add ebx, r13d
	mov r13d, ebp
	or r13d, r8d
	and r13d, eax
	mov r14d, ebp
	and r14d, r8d
	or r13d, r14d
	add ebx, r13d
	mov r13d, r12d
	xor r13d, r9d
	and r13d, r11d
	xor r13d, r9d
	add r10d, r13d
	ror r8d, 23
	ror r12d, 13
	mov r13d, r10d
	ror r13d, 23
	mov r14d, r10d
	ror r14d, 15
	xor r10d, r13d
	xor r10d, r14d
	mov r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+56]
	mov r14d, DWORD PTR [rcx+16]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+40]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+4]
	mov DWORD PTR [rcx+28], r13d
	mov r13d, ebx
	ror r13d, 20
	mov r14d, r13d
	add r14d, r10d
	add r14d, -330050500
	ror r14d, 25
	add r9d, r14d
	xor r13d, r14d
	add eax, r13d
	add r9d, DWORD PTR [rcx+12]
	mov r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+28]
	add eax, r13d
	mov r13d, ebx
	or r13d, ebp
	and r13d, r8d
	mov r14d, ebx
	and r14d, ebp
	or r13d, r14d
	add eax, r13d
	mov r13d, r11d
	xor r13d, r12d
	and r13d, r10d
	xor r13d, r12d
	add r9d, r13d
	ror ebp, 23
	ror r11d, 13
	mov r13d, r9d
	ror r13d, 23
	mov r14d, r9d
	ror r14d, 15
	xor r9d, r13d
	xor r9d, r14d
	mov r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+60]
	mov r14d, DWORD PTR [rcx+20]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+44]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+8]
	mov DWORD PTR [rcx+32], r13d
	mov r13d, eax
	ror r13d, 20
	mov r14d, r13d
	add r14d, r9d
	add r14d, -660100999
	ror r14d, 25
	add r12d, r14d
	xor r13d, r14d
	add r8d, r13d
	add r12d, DWORD PTR [rcx+16]
	mov r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+32]
	add r8d, r13d
	mov r13d, eax
	or r13d, ebx
	and r13d, ebp
	mov r14d, eax
	and r14d, ebx
	or r13d, r14d
	add r8d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r13d, r9d
	xor r13d, r11d
	add r12d, r13d
	ror ebx, 23
	ror r10d, 13
	mov r13d, r12d
	ror r13d, 23
	mov r14d, r12d
	ror r14d, 15
	xor r12d, r13d
	xor r12d, r14d
	mov r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx]
	mov r14d, DWORD PTR [rcx+24]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+48]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+12]
	mov DWORD PTR [rcx+36], r13d
	mov r13d, r8d
	ror r13d, 20
	mov r14d, r13d
	add r14d, r12d
	add r14d, -1320201997
	ror r14d, 25
	add r11d, r14d
	xor r13d, r14d
	add ebp, r13d
	add r11d, DWORD PTR [rcx+20]
	mov r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx+36]
	add ebp, r13d
	mov r13d, r8d
	or r13d, eax
	and r13d, ebx
	mov r14d, r8d
	and r14d, eax
	or r13d, r14d
	add ebp, r13d
	mov r13d, r9d
	xor r13d, r10d
	and r13d, r12d
	xor r13d, r10d
	add r11d, r13d
	ror eax, 23
	ror r9d, 13
	mov r13d, r11d
	ror r13d, 23
	mov r14d, r11d
	ror r14d, 15
	xor r11d, r13d
	xor r11d, r14d
	mov r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+4]
	mov r14d, DWORD PTR [rcx+28]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+52]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+16]
	mov DWORD PTR [rcx+40], r13d
	mov r13d, ebp
	ror r13d, 20
	mov r14d, r13d
	add r14d, r11d
	add r14d, 1654563303
	ror r14d, 25
	add r10d, r14d
	xor r13d, r14d
	add ebx, r13d
	add r10d, DWORD PTR [rcx+24]
	mov r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx+40]
	add ebx, r13d
	mov r13d, ebp
	or r13d, r8d
	and r13d, eax
	mov r14d, ebp
	and r14d, r8d
	or r13d, r14d
	add ebx, r13d
	mov r13d, r12d
	xor r13d, r9d
	and r13d, r11d
	xor r13d, r9d
	add r10d, r13d
	ror r8d, 23
	ror r12d, 13
	mov r13d, r10d
	ror r13d, 23
	mov r14d, r10d
	ror r14d, 15
	xor r10d, r13d
	xor r10d, r14d
	mov r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+8]
	mov r14d, DWORD PTR [rcx+32]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+56]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+20]
	mov DWORD PTR [rcx+44], r13d
	mov r13d, ebx
	ror r13d, 20
	mov r14d, r13d
	add r14d, r10d
	add r14d, -985840690
	ror r14d, 25
	add r9d, r14d
	xor r13d, r14d
	add eax, r13d
	add r9d, DWORD PTR [rcx+28]
	mov r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+44]
	add eax, r13d
	mov r13d, ebx
	or r13d, ebp
	and r13d, r8d
	mov r14d, ebx
	and r14d, ebp
	or r13d, r14d
	add eax, r13d
	mov r13d, r11d
	xor r13d, r12d
	and r13d, r10d
	xor r13d, r12d
	add r9d, r13d
	ror ebp, 23
	ror r11d, 13
	mov r13d, r9d
	ror r13d, 23
	mov r14d, r9d
	ror r14d, 15
	xor r9d, r13d
	xor r9d, r14d
	mov r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx+12]
	mov r14d, DWORD PTR [rcx+36]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+60]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+24]
	mov DWORD PTR [rcx+48], r13d
	mov r13d, eax
	ror r13d, 20
	mov r14d, r13d
	add r14d, r9d
	add r14d, -1971681379
	ror r14d, 25
	add r12d, r14d
	xor r13d, r14d
	add r8d, r13d
	add r12d, DWORD PTR [rcx+32]
	mov r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+48]
	add r8d, r13d
	mov r13d, eax
	or r13d, ebx
	and r13d, ebp
	mov r14d, eax
	and r14d, ebx
	or r13d, r14d
	add r8d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r13d, r9d
	xor r13d, r11d
	add r12d, r13d
	ror ebx, 23
	ror r10d, 13
	mov r13d, r12d
	ror r13d, 23
	mov r14d, r12d
	ror r14d, 15
	xor r12d, r13d
	xor r12d, r14d
	mov r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+16]
	mov r14d, DWORD PTR [rcx+40]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+28]
	mov DWORD PTR [rcx+52], r13d
	mov r13d, r8d
	ror r13d, 20
	mov r14d, r13d
	add r14d, r12d
	add r14d, 351604539
	ror r14d, 25
	add r11d, r14d
	xor r13d, r14d
	add ebp, r13d
	add r11d, DWORD PTR [rcx+36]
	mov r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx+52]
	add ebp, r13d
	mov r13d, r8d
	or r13d, eax
	and r13d, ebx
	mov r14d, r8d
	and r14d, eax
	or r13d, r14d
	add ebp, r13d
	mov r13d, r9d
	xor r13d, r10d
	and r13d, r12d
	xor r13d, r10d
	add r11d, r13d
	ror eax, 23
	ror r9d, 13
	mov r13d, r11d
	ror r13d, 23
	mov r14d, r11d
	ror r14d, 15
	xor r11d, r13d
	xor r11d, r14d
	mov r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+20]
	mov r14d, DWORD PTR [rcx+44]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+4]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+32]
	mov DWORD PTR [rcx+56], r13d
	mov r13d, ebp
	ror r13d, 20
	mov r14d, r13d
	add r14d, r11d
	add r14d, 703209078
	ror r14d, 25
	add r10d, r14d
	xor r13d, r14d
	add ebx, r13d
	add r10d, DWORD PTR [rcx+40]
	mov r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+56]
	add ebx, r13d
	mov r13d, ebp
	or r13d, r8d
	and r13d, eax
	mov r14d, ebp
	and r14d, r8d
	or r13d, r14d
	add ebx, r13d
	mov r13d, r12d
	xor r13d, r9d
	and r13d, r11d
	xor r13d, r9d
	add r10d, r13d
	ror r8d, 23
	ror r12d, 13
	mov r13d, r10d
	ror r13d, 23
	mov r14d, r10d
	ror r14d, 15
	xor r10d, r13d
	xor r10d, r14d
	mov r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+24]
	mov r14d, DWORD PTR [rcx+48]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+8]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+36]
	mov DWORD PTR [rcx+60], r13d
	mov r13d, ebx
	ror r13d, 20
	mov r14d, r13d
	add r14d, r10d
	add r14d, 1406418156
	ror r14d, 25
	add r9d, r14d
	xor r13d, r14d
	add eax, r13d
	add r9d, DWORD PTR [rcx+44]
	mov r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+60]
	add eax, r13d
	mov r13d, ebx
	or r13d, ebp
	and r13d, r8d
	mov r14d, ebx
	and r14d, ebp
	or r13d, r14d
	add eax, r13d
	mov r13d, r11d
	xor r13d, r12d
	and r13d, r10d
	xor r13d, r12d
	add r9d, r13d
	ror ebp, 23
	ror r11d, 13
	mov r13d, r9d
	ror r13d, 23
	mov r14d, r9d
	ror r14d, 15
	xor r9d, r13d
	xor r9d, r14d
	mov r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+28]
	mov r14d, DWORD PTR [rcx+52]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+12]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+40]
	mov DWORD PTR [rcx], r13d
	mov r13d, eax
	ror r13d, 20
	mov r14d, r13d
	add r14d, r9d
	add r14d, -1482130984
	ror r14d, 25
	add r12d, r14d
	xor r13d, r14d
	add r8d, r13d
	add r12d, DWORD PTR [rcx+48]
	mov r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx]
	add r8d, r13d
	mov r13d, eax
	or r13d, ebx
	and r13d, ebp
	mov r14d, eax
	and r14d, ebx
	or r13d, r14d
	add r8d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r13d, r9d
	xor r13d, r11d
	add r12d, r13d
	ror ebx, 23
	ror r10d, 13
	mov r13d, r12d
	ror r13d, 23
	mov r14d, r12d
	ror r14d, 15
	xor r12d, r13d
	xor r12d, r14d
	mov r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+32]
	mov r14d, DWORD PTR [rcx+56]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+16]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+44]
	mov DWORD PTR [rcx+4], r13d
	mov r13d, r8d
	ror r13d, 20
	mov r14d, r13d
	add r14d, r12d
	add r14d, 1330705329
	ror r14d, 25
	add r11d, r14d
	xor r13d, r14d
	add ebp, r13d
	add r11d, DWORD PTR [rcx+52]
	mov r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+4]
	add ebp, r13d
	mov r13d, r8d
	or r13d, eax
	and r13d, ebx
	mov r14d, r8d
	and r14d, eax
	or r13d, r14d
	add ebp, r13d
	mov r13d, r9d
	xor r13d, r10d
	and r13d, r12d
	xor r13d, r10d
	add r11d, r13d
	ror eax, 23
	ror r9d, 13
	mov r13d, r11d
	ror r13d, 23
	mov r14d, r11d
	ror r14d, 15
	xor r11d, r13d
	xor r11d, r14d
	mov r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx+36]
	mov r14d, DWORD PTR [rcx+60]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+20]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+48]
	mov DWORD PTR [rcx+8], r13d
	mov r13d, ebp
	ror r13d, 20
	mov r14d, r13d
	add r14d, r11d
	add r14d, -1633556638
	ror r14d, 25
	add r10d, r14d
	xor r13d, r14d
	add ebx, r13d
	add r10d, DWORD PTR [rcx+56]
	mov r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+8]
	add ebx, r13d
	mov r13d, ebp
	or r13d, r8d
	and r13d, eax
	mov r14d, ebp
	and r14d, r8d
	or r13d, r14d
	add ebx, r13d
	mov r13d, r12d
	xor r13d, r9d
	and r13d, r11d
	xor r13d, r9d
	add r10d, r13d
	ror r8d, 23
	ror r12d, 13
	mov r13d, r10d
	ror r13d, 23
	mov r14d, r10d
	ror r14d, 15
	xor r10d, r13d
	xor r10d, r14d
	mov r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+40]
	mov r14d, DWORD PTR [rcx]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+24]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+52]
	mov DWORD PTR [rcx+12], r13d
	mov r13d, ebx
	ror r13d, 20
	mov r14d, r13d
	add r14d, r10d
	add r14d, 1027854021
	ror r14d, 25
	add r9d, r14d
	xor r13d, r14d
	add eax, r13d
	add r9d, DWORD PTR [rcx+60]
	mov r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+12]
	add eax, r13d
	mov r13d, ebx
	or r13d, ebp
	and r13d, r8d
	mov r14d, ebx
	and r14d, ebp
	or r13d, r14d
	add eax, r13d
	mov r13d, r11d
	xor r13d, r12d
	and r13d, r10d
	xor r13d, r12d
	add r9d, r13d
	ror ebp, 23
	ror r11d, 13
	mov r13d, r9d
	ror r13d, 23
	mov r14d, r9d
	ror r14d, 15
	xor r9d, r13d
	xor r9d, r14d
	mov r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+44]
	mov r14d, DWORD PTR [rcx+4]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+28]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+56]
	mov DWORD PTR [rcx+16], r13d
	mov r13d, eax
	ror r13d, 20
	mov r14d, r13d
	add r14d, r9d
	add r14d, 2055708042
	ror r14d, 25
	add r12d, r14d
	xor r13d, r14d
	add r8d, r13d
	add r12d, DWORD PTR [rcx]
	mov r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+16]
	add r8d, r13d
	mov r13d, eax
	or r13d, ebx
	and r13d, ebp
	mov r14d, eax
	and r14d, ebx
	or r13d, r14d
	add r8d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r13d, r9d
	xor r13d, r11d
	add r12d, r13d
	ror ebx, 23
	ror r10d, 13
	mov r13d, r12d
	ror r13d, 23
	mov r14d, r12d
	ror r14d, 15
	xor r12d, r13d
	xor r12d, r14d
	mov r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx+48]
	mov r14d, DWORD PTR [rcx+8]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+32]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+60]
	mov DWORD PTR [rcx+20], r13d
	mov r13d, r8d
	ror r13d, 20
	mov r14d, r13d
	add r14d, r12d
	add r14d, -183551212
	ror r14d, 25
	add r11d, r14d
	xor r13d, r14d
	add ebp, r13d
	add r11d, DWORD PTR [rcx+4]
	mov r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+20]
	add ebp, r13d
	mov r13d, r8d
	or r13d, eax
	and r13d, ebx
	mov r14d, r8d
	and r14d, eax
	or r13d, r14d
	add ebp, r13d
	mov r13d, r9d
	xor r13d, r10d
	and r13d, r12d
	xor r13d, r10d
	add r11d, r13d
	ror eax, 23
	ror r9d, 13
	mov r13d, r11d
	ror r13d, 23
	mov r14d, r11d
	ror r14d, 15
	xor r11d, r13d
	xor r11d, r14d
	mov r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx+52]
	mov r14d, DWORD PTR [rcx+12]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+36]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx]
	mov DWORD PTR [rcx+24], r13d
	mov r13d, ebp
	ror r13d, 20
	mov r14d, r13d
	add r14d, r11d
	add r14d, -367102423
	ror r14d, 25
	add r10d, r14d
	xor r13d, r14d
	add ebx, r13d
	add r10d, DWORD PTR [rcx+8]
	mov r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx+24]
	add ebx, r13d
	mov r13d, ebp
	or r13d, r8d
	and r13d, eax
	mov r14d, ebp
	and r14d, r8d
	or r13d, r14d
	add ebx, r13d
	mov r13d, r12d
	xor r13d, r9d
	and r13d, r11d
	xor r13d, r9d
	add r10d, r13d
	ror r8d, 23
	ror r12d, 13
	mov r13d, r10d
	ror r13d, 23
	mov r14d, r10d
	ror r14d, 15
	xor r10d, r13d
	xor r10d, r14d
	mov r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+56]
	mov r14d, DWORD PTR [rcx+16]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+40]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+4]
	mov DWORD PTR [rcx+28], r13d
	mov r13d, ebx
	ror r13d, 20
	mov r14d, r13d
	add r14d, r10d
	add r14d, -734204845
	ror r14d, 25
	add r9d, r14d
	xor r13d, r14d
	add eax, r13d
	add r9d, DWORD PTR [rcx+12]
	mov r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+28]
	add eax, r13d
	mov r13d, ebx
	or r13d, ebp
	and r13d, r8d
	mov r14d, ebx
	and r14d, ebp
	or r13d, r14d
	add eax, r13d
	mov r13d, r11d
	xor r13d, r12d
	and r13d, r10d
	xor r13d, r12d
	add r9d, r13d
	ror ebp, 23
	ror r11d, 13
	mov r13d, r9d
	ror r13d, 23
	mov r14d, r9d
	ror r14d, 15
	xor r9d, r13d
	xor r9d, r14d
	mov r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+60]
	mov r14d, DWORD PTR [rcx+20]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+44]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+8]
	mov DWORD PTR [rcx+32], r13d
	mov r13d, eax
	ror r13d, 20
	mov r14d, r13d
	add r14d, r9d
	add r14d, -1468409689
	ror r14d, 25
	add r12d, r14d
	xor r13d, r14d
	add r8d, r13d
	add r12d, DWORD PTR [rcx+16]
	mov r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+32]
	add r8d, r13d
	mov r13d, eax
	or r13d, ebx
	and r13d, ebp
	mov r14d, eax
	and r14d, ebx
	or r13d, r14d
	add r8d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r13d, r9d
	xor r13d, r11d
	add r12d, r13d
	ror ebx, 23
	ror r10d, 13
	mov r13d, r12d
	ror r13d, 23
	mov r14d, r12d
	ror r14d, 15
	xor r12d, r13d
	xor r12d, r14d
	mov r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx]
	mov r14d, DWORD PTR [rcx+24]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+48]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+12]
	mov DWORD PTR [rcx+36], r13d
	mov r13d, r8d
	ror r13d, 20
	mov r14d, r13d
	add r14d, r12d
	add r14d, 1358147919
	ror r14d, 25
	add r11d, r14d
	xor r13d, r14d
	add ebp, r13d
	add r11d, DWORD PTR [rcx+20]
	mov r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx+36]
	add ebp, r13d
	mov r13d, r8d
	or r13d, eax
	and r13d, ebx
	mov r14d, r8d
	and r14d, eax
	or r13d, r14d
	add ebp, r13d
	mov r13d, r9d
	xor r13d, r10d
	and r13d, r12d
	xor r13d, r10d
	add r11d, r13d
	ror eax, 23
	ror r9d, 13
	mov r13d, r11d
	ror r13d, 23
	mov r14d, r11d
	ror r14d, 15
	xor r11d, r13d
	xor r11d, r14d
	mov r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+4]
	mov r14d, DWORD PTR [rcx+28]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+52]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+16]
	mov DWORD PTR [rcx+40], r13d
	mov r13d, ebp
	ror r13d, 20
	mov r14d, r13d
	add r14d, r11d
	add r14d, -1578671458
	ror r14d, 25
	add r10d, r14d
	xor r13d, r14d
	add ebx, r13d
	add r10d, DWORD PTR [rcx+24]
	mov r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx+40]
	add ebx, r13d
	mov r13d, ebp
	or r13d, r8d
	and r13d, eax
	mov r14d, ebp
	and r14d, r8d
	or r13d, r14d
	add ebx, r13d
	mov r13d, r12d
	xor r13d, r9d
	and r13d, r11d
	xor r13d, r9d
	add r10d, r13d
	ror r8d, 23
	ror r12d, 13
	mov r13d, r10d
	ror r13d, 23
	mov r14d, r10d
	ror r14d, 15
	xor r10d, r13d
	xor r10d, r14d
	mov r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+8]
	mov r14d, DWORD PTR [rcx+32]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+56]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+20]
	mov DWORD PTR [rcx+44], r13d
	mov r13d, ebx
	ror r13d, 20
	mov r14d, r13d
	add r14d, r10d
	add r14d, 1137624381
	ror r14d, 25
	add r9d, r14d
	xor r13d, r14d
	add eax, r13d
	add r9d, DWORD PTR [rcx+28]
	mov r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+44]
	add eax, r13d
	mov r13d, ebx
	or r13d, ebp
	and r13d, r8d
	mov r14d, ebx
	and r14d, ebp
	or r13d, r14d
	add eax, r13d
	mov r13d, r11d
	xor r13d, r12d
	and r13d, r10d
	xor r13d, r12d
	add r9d, r13d
	ror ebp, 23
	ror r11d, 13
	mov r13d, r9d
	ror r13d, 23
	mov r14d, r9d
	ror r14d, 15
	xor r9d, r13d
	xor r9d, r14d
	mov r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx+12]
	mov r14d, DWORD PTR [rcx+36]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+60]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+24]
	mov DWORD PTR [rcx+48], r13d
	mov r13d, eax
	ror r13d, 20
	mov r14d, r13d
	add r14d, r9d
	add r14d, -2019718534
	ror r14d, 25
	add r12d, r14d
	xor r13d, r14d
	add r8d, r13d
	add r12d, DWORD PTR [rcx+32]
	mov r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+48]
	add r8d, r13d
	mov r13d, eax
	or r13d, ebx
	and r13d, ebp
	mov r14d, eax
	and r14d, ebx
	or r13d, r14d
	add r8d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r13d, r9d
	xor r13d, r11d
	add r12d, r13d
	ror ebx, 23
	ror r10d, 13
	mov r13d, r12d
	ror r13d, 23
	mov r14d, r12d
	ror r14d, 15
	xor r12d, r13d
	xor r12d, r14d
	mov r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+16]
	mov r14d, DWORD PTR [rcx+40]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+28]
	mov DWORD PTR [rcx+52], r13d
	mov r13d, r8d
	ror r13d, 20
	mov r14d, r13d
	add r14d, r12d
	add r14d, 255530229
	ror r14d, 25
	add r11d, r14d
	xor r13d, r14d
	add ebp, r13d
	add r11d, DWORD PTR [rcx+36]
	mov r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx+52]
	add ebp, r13d
	mov r13d, r8d
	or r13d, eax
	and r13d, ebx
	mov r14d, r8d
	and r14d, eax
	or r13d, r14d
	add ebp, r13d
	mov r13d, r9d
	xor r13d, r10d
	and r13d, r12d
	xor r13d, r10d
	add r11d, r13d
	ror eax, 23
	ror r9d, 13
	mov r13d, r11d
	ror r13d, 23
	mov r14d, r11d
	ror r14d, 15
	xor r11d, r13d
	xor r11d, r14d
	mov r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+20]
	mov r14d, DWORD PTR [rcx+44]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+4]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+32]
	mov DWORD PTR [rcx+56], r13d
	mov r13d, ebp
	ror r13d, 20
	mov r14d, r13d
	add r14d, r11d
	add r14d, 511060458
	ror r14d, 25
	add r10d, r14d
	xor r13d, r14d
	add ebx, r13d
	add r10d, DWORD PTR [rcx+40]
	mov r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+56]
	add ebx, r13d
	mov r13d, ebp
	or r13d, r8d
	and r13d, eax
	mov r14d, ebp
	and r14d, r8d
	or r13d, r14d
	add ebx, r13d
	mov r13d, r12d
	xor r13d, r9d
	and r13d, r11d
	xor r13d, r9d
	add r10d, r13d
	ror r8d, 23
	ror r12d, 13
	mov r13d, r10d
	ror r13d, 23
	mov r14d, r10d
	ror r14d, 15
	xor r10d, r13d
	xor r10d, r14d
	mov r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+24]
	mov r14d, DWORD PTR [rcx+48]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+8]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+36]
	mov DWORD PTR [rcx+60], r13d
	mov r13d, ebx
	ror r13d, 20
	mov r14d, r13d
	add r14d, r10d
	add r14d, 1022120916
	ror r14d, 25
	add r9d, r14d
	xor r13d, r14d
	add eax, r13d
	add r9d, DWORD PTR [rcx+44]
	mov r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+60]
	add eax, r13d
	mov r13d, ebx
	or r13d, ebp
	and r13d, r8d
	mov r14d, ebx
	and r14d, ebp
	or r13d, r14d
	add eax, r13d
	mov r13d, r11d
	xor r13d, r12d
	and r13d, r10d
	xor r13d, r12d
	add r9d, r13d
	ror ebp, 23
	ror r11d, 13
	mov r13d, r9d
	ror r13d, 23
	mov r14d, r9d
	ror r14d, 15
	xor r9d, r13d
	xor r9d, r14d
	mov r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+28]
	mov r14d, DWORD PTR [rcx+52]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+12]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+40]
	mov DWORD PTR [rcx], r13d
	mov r13d, eax
	ror r13d, 20
	mov r14d, r13d
	add r14d, r9d
	add r14d, 2044241832
	ror r14d, 25
	add r12d, r14d
	xor r13d, r14d
	add r8d, r13d
	add r12d, DWORD PTR [rcx+48]
	mov r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx]
	add r8d, r13d
	mov r13d, eax
	or r13d, ebx
	and r13d, ebp
	mov r14d, eax
	and r14d, ebx
	or r13d, r14d
	add r8d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r13d, r9d
	xor r13d, r11d
	add r12d, r13d
	ror ebx, 23
	ror r10d, 13
	mov r13d, r12d
	ror r13d, 23
	mov r14d, r12d
	ror r14d, 15
	xor r12d, r13d
	xor r12d, r14d
	mov r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+32]
	mov r14d, DWORD PTR [rcx+56]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+16]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+44]
	mov DWORD PTR [rcx+4], r13d
	mov r13d, r8d
	ror r13d, 20
	mov r14d, r13d
	add r14d, r12d
	add r14d, -206483632
	ror r14d, 25
	add r11d, r14d
	xor r13d, r14d
	add ebp, r13d
	add r11d, DWORD PTR [rcx+52]
	mov r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+4]
	add ebp, r13d
	mov r13d, r8d
	or r13d, eax
	and r13d, ebx
	mov r14d, r8d
	and r14d, eax
	or r13d, r14d
	add ebp, r13d
	mov r13d, r9d
	xor r13d, r10d
	and r13d, r12d
	xor r13d, r10d
	add r11d, r13d
	ror eax, 23
	ror r9d, 13
	mov r13d, r11d
	ror r13d, 23
	mov r14d, r11d
	ror r14d, 15
	xor r11d, r13d
	xor r11d, r14d
	mov r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx+36]
	mov r14d, DWORD PTR [rcx+60]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+20]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+48]
	mov DWORD PTR [rcx+8], r13d
	mov r13d, ebp
	ror r13d, 20
	mov r14d, r13d
	add r14d, r11d
	add r14d, -412967263
	ror r14d, 25
	add r10d, r14d
	xor r13d, r14d
	add ebx, r13d
	add r10d, DWORD PTR [rcx+56]
	mov r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+8]
	add ebx, r13d
	mov r13d, ebp
	or r13d, r8d
	and r13d, eax
	mov r14d, ebp
	and r14d, r8d
	or r13d, r14d
	add ebx, r13d
	mov r13d, r12d
	xor r13d, r9d
	and r13d, r11d
	xor r13d, r9d
	add r10d, r13d
	ror r8d, 23
	ror r12d, 13
	mov r13d, r10d
	ror r13d, 23
	mov r14d, r10d
	ror r14d, 15
	xor r10d, r13d
	xor r10d, r14d
	mov r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+40]
	mov r14d, DWORD PTR [rcx]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+24]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+52]
	mov DWORD PTR [rcx+12], r13d
	mov r13d, ebx
	ror r13d, 20
	mov r14d, r13d
	add r14d, r10d
	add r14d, -825934525
	ror r14d, 25
	add r9d, r14d
	xor r13d, r14d
	add eax, r13d
	add r9d, DWORD PTR [rcx+60]
	mov r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+12]
	add eax, r13d
	mov r13d, ebx
	or r13d, ebp
	and r13d, r8d
	mov r14d, ebx
	and r14d, ebp
	or r13d, r14d
	add eax, r13d
	mov r13d, r11d
	xor r13d, r12d
	and r13d, r10d
	xor r13d, r12d
	add r9d, r13d
	ror ebp, 23
	ror r11d, 13
	mov r13d, r9d
	ror r13d, 23
	mov r14d, r9d
	ror r14d, 15
	xor r9d, r13d
	xor r9d, r14d
	mov r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+44]
	mov r14d, DWORD PTR [rcx+4]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+28]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+56]
	mov DWORD PTR [rcx+16], r13d
	mov r13d, eax
	ror r13d, 20
	mov r14d, r13d
	add r14d, r9d
	add r14d, -1651869049
	ror r14d, 25
	add r12d, r14d
	xor r13d, r14d
	add r8d, r13d
	add r12d, DWORD PTR [rcx]
	mov r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+16]
	add r8d, r13d
	mov r13d, eax
	or r13d, ebx
	and r13d, ebp
	mov r14d, eax
	and r14d, ebx
	or r13d, r14d
	add r8d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r13d, r9d
	xor r13d, r11d
	add r12d, r13d
	ror ebx, 23
	ror r10d, 13
	mov r13d, r12d
	ror r13d, 23
	mov r14d, r12d
	ror r14d, 15
	xor r12d, r13d
	xor r12d, r14d
	mov r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx+48]
	mov r14d, DWORD PTR [rcx+8]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+32]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+60]
	mov DWORD PTR [rcx+20], r13d
	mov r13d, r8d
	ror r13d, 20
	mov r14d, r13d
	add r14d, r12d
	add r14d, 991229199
	ror r14d, 25
	add r11d, r14d
	xor r13d, r14d
	add ebp, r13d
	add r11d, DWORD PTR [rcx+4]
	mov r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+20]
	add ebp, r13d
	mov r13d, r8d
	or r13d, eax
	and r13d, ebx
	mov r14d, r8d
	and r14d, eax
	or r13d, r14d
	add ebp, r13d
	mov r13d, r9d
	xor r13d, r10d
	and r13d, r12d
	xor r13d, r10d
	add r11d, r13d
	ror eax, 23
	ror r9d, 13
	mov r13d, r11d
	ror r13d, 23
	mov r14d, r11d
	ror r14d, 15
	xor r11d, r13d
	xor r11d, r14d
	mov r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx+52]
	mov r14d, DWORD PTR [rcx+12]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+36]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx]
	mov DWORD PTR [rcx+24], r13d
	mov r13d, ebp
	ror r13d, 20
	mov r14d, r13d
	add r14d, r11d
	add r14d, 1982458398
	ror r14d, 25
	add r10d, r14d
	xor r13d, r14d
	add ebx, r13d
	add r10d, DWORD PTR [rcx+8]
	mov r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx+24]
	add ebx, r13d
	mov r13d, ebp
	or r13d, r8d
	and r13d, eax
	mov r14d, ebp
	and r14d, r8d
	or r13d, r14d
	add ebx, r13d
	mov r13d, r12d
	xor r13d, r9d
	and r13d, r11d
	xor r13d, r9d
	add r10d, r13d
	ror r8d, 23
	ror r12d, 13
	mov r13d, r10d
	ror r13d, 23
	mov r14d, r10d
	ror r14d, 15
	xor r10d, r13d
	xor r10d, r14d
	mov r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+56]
	mov r14d, DWORD PTR [rcx+16]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+40]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+4]
	mov DWORD PTR [rcx+28], r13d
	mov r13d, ebx
	ror r13d, 20
	mov r14d, r13d
	add r14d, r10d
	add r14d, -330050500
	ror r14d, 25
	add r9d, r14d
	xor r13d, r14d
	add eax, r13d
	add r9d, DWORD PTR [rcx+12]
	mov r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+28]
	add eax, r13d
	mov r13d, ebx
	or r13d, ebp
	and r13d, r8d
	mov r14d, ebx
	and r14d, ebp
	or r13d, r14d
	add eax, r13d
	mov r13d, r11d
	xor r13d, r12d
	and r13d, r10d
	xor r13d, r12d
	add r9d, r13d
	ror ebp, 23
	ror r11d, 13
	mov r13d, r9d
	ror r13d, 23
	mov r14d, r9d
	ror r14d, 15
	xor r9d, r13d
	xor r9d, r14d
	mov r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+60]
	mov r14d, DWORD PTR [rcx+20]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+44]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+8]
	mov DWORD PTR [rcx+32], r13d
	mov r13d, eax
	ror r13d, 20
	mov r14d, r13d
	add r14d, r9d
	add r14d, -660100999
	ror r14d, 25
	add r12d, r14d
	xor r13d, r14d
	add r8d, r13d
	add r12d, DWORD PTR [rcx+16]
	mov r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+32]
	add r8d, r13d
	mov r13d, eax
	or r13d, ebx
	and r13d, ebp
	mov r14d, eax
	and r14d, ebx
	or r13d, r14d
	add r8d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r13d, r9d
	xor r13d, r11d
	add r12d, r13d
	ror ebx, 23
	ror r10d, 13
	mov r13d, r12d
	ror r13d, 23
	mov r14d, r12d
	ror r14d, 15
	xor r12d, r13d
	xor r12d, r14d
	mov r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx]
	mov r14d, DWORD PTR [rcx+24]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+48]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+12]
	mov DWORD PTR [rcx+36], r13d
	mov r13d, r8d
	ror r13d, 20
	mov r14d, r13d
	add r14d, r12d
	add r14d, -1320201997
	ror r14d, 25
	add r11d, r14d
	xor r13d, r14d
	add ebp, r13d
	add r11d, DWORD PTR [rcx+20]
	mov r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx+36]
	add ebp, r13d
	mov r13d, r8d
	or r13d, eax
	and r13d, ebx
	mov r14d, r8d
	and r14d, eax
	or r13d, r14d
	add ebp, r13d
	mov r13d, r9d
	xor r13d, r10d
	and r13d, r12d
	xor r13d, r10d
	add r11d, r13d
	ror eax, 23
	ror r9d, 13
	mov r13d, r11d
	ror r13d, 23
	mov r14d, r11d
	ror r14d, 15
	xor r11d, r13d
	xor r11d, r14d
	mov r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+4]
	mov r14d, DWORD PTR [rcx+28]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+52]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+16]
	mov DWORD PTR [rcx+40], r13d
	mov r13d, ebp
	ror r13d, 20
	mov r14d, r13d
	add r14d, r11d
	add r14d, 1654563303
	ror r14d, 25
	add r10d, r14d
	xor r13d, r14d
	add ebx, r13d
	add r10d, DWORD PTR [rcx+24]
	mov r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx+40]
	add ebx, r13d
	mov r13d, ebp
	or r13d, r8d
	and r13d, eax
	mov r14d, ebp
	and r14d, r8d
	or r13d, r14d
	add ebx, r13d
	mov r13d, r12d
	xor r13d, r9d
	and r13d, r11d
	xor r13d, r9d
	add r10d, r13d
	ror r8d, 23
	ror r12d, 13
	mov r13d, r10d
	ror r13d, 23
	mov r14d, r10d
	ror r14d, 15
	xor r10d, r13d
	xor r10d, r14d
	mov r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+8]
	mov r14d, DWORD PTR [rcx+32]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+56]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+20]
	mov DWORD PTR [rcx+44], r13d
	mov r13d, ebx
	ror r13d, 20
	mov r14d, r13d
	add r14d, r10d
	add r14d, -985840690
	ror r14d, 25
	add r9d, r14d
	xor r13d, r14d
	add eax, r13d
	add r9d, DWORD PTR [rcx+28]
	mov r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+44]
	add eax, r13d
	mov r13d, ebx
	or r13d, ebp
	and r13d, r8d
	mov r14d, ebx
	and r14d, ebp
	or r13d, r14d
	add eax, r13d
	mov r13d, r11d
	xor r13d, r12d
	and r13d, r10d
	xor r13d, r12d
	add r9d, r13d
	ror ebp, 23
	ror r11d, 13
	mov r13d, r9d
	ror r13d, 23
	mov r14d, r9d
	ror r14d, 15
	xor r9d, r13d
	xor r9d, r14d
	mov r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx+12]
	mov r14d, DWORD PTR [rcx+36]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+60]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+24]
	mov DWORD PTR [rcx+48], r13d
	mov r13d, eax
	ror r13d, 20
	mov r14d, r13d
	add r14d, r9d
	add r14d, -1971681379
	ror r14d, 25
	add r12d, r14d
	xor r13d, r14d
	add r8d, r13d
	add r12d, DWORD PTR [rcx+32]
	mov r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+48]
	add r8d, r13d
	mov r13d, eax
	or r13d, ebx
	and r13d, ebp
	mov r14d, eax
	and r14d, ebx
	or r13d, r14d
	add r8d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r13d, r9d
	xor r13d, r11d
	add r12d, r13d
	ror ebx, 23
	ror r10d, 13
	mov r13d, r12d
	ror r13d, 23
	mov r14d, r12d
	ror r14d, 15
	xor r12d, r13d
	xor r12d, r14d
	mov r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+16]
	mov r14d, DWORD PTR [rcx+40]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+28]
	mov DWORD PTR [rcx+52], r13d
	mov r13d, r8d
	ror r13d, 20
	mov r14d, r13d
	add r14d, r12d
	add r14d, 351604539
	ror r14d, 25
	add r11d, r14d
	xor r13d, r14d
	add ebp, r13d
	add r11d, DWORD PTR [rcx+36]
	mov r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx+52]
	add ebp, r13d
	mov r13d, r8d
	or r13d, eax
	and r13d, ebx
	mov r14d, r8d
	and r14d, eax
	or r13d, r14d
	add ebp, r13d
	mov r13d, r9d
	xor r13d, r10d
	and r13d, r12d
	xor r13d, r10d
	add r11d, r13d
	ror eax, 23
	ror r9d, 13
	mov r13d, r11d
	ror r13d, 23
	mov r14d, r11d
	ror r14d, 15
	xor r11d, r13d
	xor r11d, r14d
	mov r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+20]
	mov r14d, DWORD PTR [rcx+44]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+4]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+32]
	mov DWORD PTR [rcx+56], r13d
	mov r13d, ebp
	ror r13d, 20
	mov r14d, r13d
	add r14d, r11d
	add r14d, 703209078
	ror r14d, 25
	add r10d, r14d
	xor r13d, r14d
	add ebx, r13d
	add r10d, DWORD PTR [rcx+40]
	mov r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+56]
	add ebx, r13d
	mov r13d, ebp
	or r13d, r8d
	and r13d, eax
	mov r14d, ebp
	and r14d, r8d
	or r13d, r14d
	add ebx, r13d
	mov r13d, r12d
	xor r13d, r9d
	and r13d, r11d
	xor r13d, r9d
	add r10d, r13d
	ror r8d, 23
	ror r12d, 13
	mov r13d, r10d
	ror r13d, 23
	mov r14d, r10d
	ror r14d, 15
	xor r10d, r13d
	xor r10d, r14d
	mov r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+24]
	mov r14d, DWORD PTR [rcx+48]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+8]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+36]
	mov DWORD PTR [rcx+60], r13d
	mov r13d, ebx
	ror r13d, 20
	mov r14d, r13d
	add r14d, r10d
	add r14d, 1406418156
	ror r14d, 25
	add r9d, r14d
	xor r13d, r14d
	add eax, r13d
	add r9d, DWORD PTR [rcx+44]
	mov r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+60]
	add eax, r13d
	mov r13d, ebx
	or r13d, ebp
	and r13d, r8d
	mov r14d, ebx
	and r14d, ebp
	or r13d, r14d
	add eax, r13d
	mov r13d, r11d
	xor r13d, r12d
	and r13d, r10d
	xor r13d, r12d
	add r9d, r13d
	ror ebp, 23
	ror r11d, 13
	mov r13d, r9d
	ror r13d, 23
	mov r14d, r9d
	ror r14d, 15
	xor r9d, r13d
	xor r9d, r14d
	mov r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+28]
	mov r14d, DWORD PTR [rcx+52]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+12]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+40]
	mov DWORD PTR [rcx], r13d
	mov r13d, eax
	ror r13d, 20
	mov r14d, r13d
	add r14d, r9d
	add r14d, -1482130984
	ror r14d, 25
	add r12d, r14d
	xor r13d, r14d
	add r8d, r13d
	add r12d, DWORD PTR [rcx+48]
	mov r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx]
	add r8d, r13d
	mov r13d, eax
	or r13d, ebx
	and r13d, ebp
	mov r14d, eax
	and r14d, ebx
	or r13d, r14d
	add r8d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r13d, r9d
	xor r13d, r11d
	add r12d, r13d
	ror ebx, 23
	ror r10d, 13
	mov r13d, r12d
	ror r13d, 23
	mov r14d, r12d
	ror r14d, 15
	xor r12d, r13d
	xor r12d, r14d
	mov r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+32]
	mov r14d, DWORD PTR [rcx+56]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+16]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+44]
	mov DWORD PTR [rcx+4], r13d
	mov r13d, r8d
	ror r13d, 20
	mov r14d, r13d
	add r14d, r12d
	add r14d, 1330705329
	ror r14d, 25
	add r11d, r14d
	xor r13d, r14d
	add ebp, r13d
	add r11d, DWORD PTR [rcx+52]
	mov r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+4]
	add ebp, r13d
	mov r13d, r8d
	or r13d, eax
	and r13d, ebx
	mov r14d, r8d
	and r14d, eax
	or r13d, r14d
	add ebp, r13d
	mov r13d, r9d
	xor r13d, r10d
	and r13d, r12d
	xor r13d, r10d
	add r11d, r13d
	ror eax, 23
	ror r9d, 13
	mov r13d, r11d
	ror r13d, 23
	mov r14d, r11d
	ror r14d, 15
	xor r11d, r13d
	xor r11d, r14d
	mov r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx+36]
	mov r14d, DWORD PTR [rcx+60]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+20]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+48]
	mov DWORD PTR [rcx+8], r13d
	mov r13d, ebp
	ror r13d, 20
	mov r14d, r13d
	add r14d, r11d
	add r14d, -1633556638
	ror r14d, 25
	add r10d, r14d
	xor r13d, r14d
	add ebx, r13d
	add r10d, DWORD PTR [rcx+56]
	mov r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+8]
	add ebx, r13d
	mov r13d, ebp
	or r13d, r8d
	and r13d, eax
	mov r14d, ebp
	and r14d, r8d
	or r13d, r14d
	add ebx, r13d
	mov r13d, r12d
	xor r13d, r9d
	and r13d, r11d
	xor r13d, r9d
	add r10d, r13d
	ror r8d, 23
	ror r12d, 13
	mov r13d, r10d
	ror r13d, 23
	mov r14d, r10d
	ror r14d, 15
	xor r10d, r13d
	xor r10d, r14d
	mov r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+40]
	mov r14d, DWORD PTR [rcx]
	ror r14d, 17
	xor r13d, r14d
	mov r14d, r13d
	ror r14d, 17
	mov r15d, r13d
	ror r15d, 9
	xor r13d, r14d
	xor r13d, r15d
	mov r14d, DWORD PTR [rcx+24]
	ror r14d, 25
	xor r13d, r14d
	xor r13d, DWORD PTR [rcx+52]
	mov DWORD PTR [rcx+12], r13d
	mov r13d, ebx
	ror r13d, 20
	mov r14d, r13d
	add r14d, r10d
	add r14d, 1027854021
	ror r14d, 25
	add r9d, r14d
	xor r13d, r14d
	add eax, r13d
	add r9d, DWORD PTR [rcx+60]
	mov r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+12]
	add eax, r13d
	mov r13d, ebx
	or r13d, ebp
	and r13d, r8d
	mov r14d, ebx
	and r14d, ebp
	or r13d, r14d
	add eax, r13d
	mov r13d, r11d
	xor r13d, r12d
	and r13d, r10d
	xor r13d, r12d
	add r9d, r13d
	ror ebp, 23
	ror r11d, 13
	mov r13d, r9d
	ror r13d, 23
	mov r14d, r9d
	ror r14d, 15
	xor r9d, r13d
	xor r9d, r14d
	xor eax, DWORD PTR [rdi]
	xor ebx, DWORD PTR [rdi+4]
	xor ebp, DWORD PTR [rdi+8]
	xor r8d, DWORD PTR [rdi+12]
	xor r9d, DWORD PTR [rdi+16]
	xor r10d, DWORD PTR [rdi+20]
	xor r11d, DWORD PTR [rdi+24]
	xor r12d, DWORD PTR [rdi+28]
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

vg_sm3_init:
	mov eax, 1937774191
	mov DWORD PTR [rdi], eax
	mov eax, 1226093241
	mov DWORD PTR [rdi+4], eax
	mov eax, 388252375
	mov DWORD PTR [rdi+8], eax
	mov eax, -628488704
	mov DWORD PTR [rdi+12], eax
	mov eax, -1452330820
	mov DWORD PTR [rdi+16], eax
	mov eax, 372324522
	mov DWORD PTR [rdi+20], eax
	mov eax, -477237683
	mov DWORD PTR [rdi+24], eax
	mov eax, -1325724082
	mov DWORD PTR [rdi+28], eax
	ret
	.p2align 6

vg_sm3_update:
	lea rsp, [rsp-168]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+112], rbx
	mov QWORD PTR [r8+120], rbp
	mov QWORD PTR [r8+128], r12
	mov QWORD PTR [r8+136], r13
	mov QWORD PTR [r8+144], r14
	mov QWORD PTR [r8+152], r15
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
	call {vg_sm3_compress}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+112]
	mov rbp, QWORD PTR [r15+120]
	mov r12, QWORD PTR [r15+128]
	mov r13, QWORD PTR [r15+136]
	mov r14, QWORD PTR [r15+144]
	mov r15, QWORD PTR [r15+152]
	lea rsp, [rsp+168]
	ret
	.p2align 6

vg_sm3_finalize:
	lea rsp, [rsp-168]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+112], rbx
	mov QWORD PTR [rcx+120], rbp
	mov QWORD PTR [rcx+128], r12
	mov QWORD PTR [rcx+136], r13
	mov QWORD PTR [rcx+144], r14
	mov QWORD PTR [rcx+152], r15
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
	call {vg_sm3_compress}
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
	mov rbx, QWORD PTR [r15+112]
	mov rbp, QWORD PTR [r15+120]
	mov r12, QWORD PTR [r15+128]
	mov r13, QWORD PTR [r15+136]
	mov r14, QWORD PTR [r15+144]
	mov r15, QWORD PTR [r15+152]
	lea rsp, [rsp+168]
	ret
	.p2align 6
