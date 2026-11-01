// The functions of `src/sha512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_compress:
	mov QWORD PTR [rcx+128], rbx
	mov QWORD PTR [rcx+136], rbp
	mov QWORD PTR [rcx+144], r12
	mov QWORD PTR [rcx+152], r13
	mov QWORD PTR [rcx+160], r14
	mov QWORD PTR [rcx+168], r15
	test rdx, rdx
	je 20f
22:
	mov rax, QWORD PTR [rdi]
	mov rbx, QWORD PTR [rdi+8]
	mov rbp, QWORD PTR [rdi+16]
	mov r8, QWORD PTR [rdi+24]
	mov r9, QWORD PTR [rdi+32]
	mov r10, QWORD PTR [rdi+40]
	mov r11, QWORD PTR [rdi+48]
	mov r12, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+176], rsi
	mov QWORD PTR [rcx+184], rdx
	mov rdx, rsi
	lea rsi, {VG_SHA512_K}
	mov r13, QWORD PTR [rdx]
	bswap r13
	mov QWORD PTR [rcx], r13
	add r12, QWORD PTR [rsi]
	add r12, r13
	mov r14, r9
	ror r14, 14
	mov r15, r9
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r12, r14
	mov r14, r10
	xor r14, r11
	and r14, r9
	xor r14, r11
	add r12, r14
	add r8, r12
	mov r14, rax
	ror r14, 28
	mov r15, rax
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r12, r14
	mov r14, rax
	or r14, rbx
	and r14, rbp
	mov r15, rax
	and r15, rbx
	or r14, r15
	add r12, r14
	mov r13, QWORD PTR [rdx+8]
	bswap r13
	mov QWORD PTR [rcx+8], r13
	add r11, QWORD PTR [rsi+8]
	add r11, r13
	mov r14, r8
	ror r14, 14
	mov r15, r8
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r11, r14
	mov r14, r9
	xor r14, r10
	and r14, r8
	xor r14, r10
	add r11, r14
	add rbp, r11
	mov r14, r12
	ror r14, 28
	mov r15, r12
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r11, r14
	mov r14, r12
	or r14, rax
	and r14, rbx
	mov r15, r12
	and r15, rax
	or r14, r15
	add r11, r14
	mov r13, QWORD PTR [rdx+16]
	bswap r13
	mov QWORD PTR [rcx+16], r13
	add r10, QWORD PTR [rsi+16]
	add r10, r13
	mov r14, rbp
	ror r14, 14
	mov r15, rbp
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r10, r14
	mov r14, r8
	xor r14, r9
	and r14, rbp
	xor r14, r9
	add r10, r14
	add rbx, r10
	mov r14, r11
	ror r14, 28
	mov r15, r11
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r10, r14
	mov r14, r11
	or r14, r12
	and r14, rax
	mov r15, r11
	and r15, r12
	or r14, r15
	add r10, r14
	mov r13, QWORD PTR [rdx+24]
	bswap r13
	mov QWORD PTR [rcx+24], r13
	add r9, QWORD PTR [rsi+24]
	add r9, r13
	mov r14, rbx
	ror r14, 14
	mov r15, rbx
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r9, r14
	mov r14, rbp
	xor r14, r8
	and r14, rbx
	xor r14, r8
	add r9, r14
	add rax, r9
	mov r14, r10
	ror r14, 28
	mov r15, r10
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r9, r14
	mov r14, r10
	or r14, r11
	and r14, r12
	mov r15, r10
	and r15, r11
	or r14, r15
	add r9, r14
	mov r13, QWORD PTR [rdx+32]
	bswap r13
	mov QWORD PTR [rcx+32], r13
	add r8, QWORD PTR [rsi+32]
	add r8, r13
	mov r14, rax
	ror r14, 14
	mov r15, rax
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r8, r14
	mov r14, rbx
	xor r14, rbp
	and r14, rax
	xor r14, rbp
	add r8, r14
	add r12, r8
	mov r14, r9
	ror r14, 28
	mov r15, r9
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r8, r14
	mov r14, r9
	or r14, r10
	and r14, r11
	mov r15, r9
	and r15, r10
	or r14, r15
	add r8, r14
	mov r13, QWORD PTR [rdx+40]
	bswap r13
	mov QWORD PTR [rcx+40], r13
	add rbp, QWORD PTR [rsi+40]
	add rbp, r13
	mov r14, r12
	ror r14, 14
	mov r15, r12
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add rbp, r14
	mov r14, rax
	xor r14, rbx
	and r14, r12
	xor r14, rbx
	add rbp, r14
	add r11, rbp
	mov r14, r8
	ror r14, 28
	mov r15, r8
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add rbp, r14
	mov r14, r8
	or r14, r9
	and r14, r10
	mov r15, r8
	and r15, r9
	or r14, r15
	add rbp, r14
	mov r13, QWORD PTR [rdx+48]
	bswap r13
	mov QWORD PTR [rcx+48], r13
	add rbx, QWORD PTR [rsi+48]
	add rbx, r13
	mov r14, r11
	ror r14, 14
	mov r15, r11
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add rbx, r14
	mov r14, r12
	xor r14, rax
	and r14, r11
	xor r14, rax
	add rbx, r14
	add r10, rbx
	mov r14, rbp
	ror r14, 28
	mov r15, rbp
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add rbx, r14
	mov r14, rbp
	or r14, r8
	and r14, r9
	mov r15, rbp
	and r15, r8
	or r14, r15
	add rbx, r14
	mov r13, QWORD PTR [rdx+56]
	bswap r13
	mov QWORD PTR [rcx+56], r13
	add rax, QWORD PTR [rsi+56]
	add rax, r13
	mov r14, r10
	ror r14, 14
	mov r15, r10
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add rax, r14
	mov r14, r11
	xor r14, r12
	and r14, r10
	xor r14, r12
	add rax, r14
	add r9, rax
	mov r14, rbx
	ror r14, 28
	mov r15, rbx
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add rax, r14
	mov r14, rbx
	or r14, rbp
	and r14, r8
	mov r15, rbx
	and r15, rbp
	or r14, r15
	add rax, r14
	mov r13, QWORD PTR [rdx+64]
	bswap r13
	mov QWORD PTR [rcx+64], r13
	add r12, QWORD PTR [rsi+64]
	add r12, r13
	mov r14, r9
	ror r14, 14
	mov r15, r9
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r12, r14
	mov r14, r10
	xor r14, r11
	and r14, r9
	xor r14, r11
	add r12, r14
	add r8, r12
	mov r14, rax
	ror r14, 28
	mov r15, rax
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r12, r14
	mov r14, rax
	or r14, rbx
	and r14, rbp
	mov r15, rax
	and r15, rbx
	or r14, r15
	add r12, r14
	mov r13, QWORD PTR [rdx+72]
	bswap r13
	mov QWORD PTR [rcx+72], r13
	add r11, QWORD PTR [rsi+72]
	add r11, r13
	mov r14, r8
	ror r14, 14
	mov r15, r8
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r11, r14
	mov r14, r9
	xor r14, r10
	and r14, r8
	xor r14, r10
	add r11, r14
	add rbp, r11
	mov r14, r12
	ror r14, 28
	mov r15, r12
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r11, r14
	mov r14, r12
	or r14, rax
	and r14, rbx
	mov r15, r12
	and r15, rax
	or r14, r15
	add r11, r14
	mov r13, QWORD PTR [rdx+80]
	bswap r13
	mov QWORD PTR [rcx+80], r13
	add r10, QWORD PTR [rsi+80]
	add r10, r13
	mov r14, rbp
	ror r14, 14
	mov r15, rbp
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r10, r14
	mov r14, r8
	xor r14, r9
	and r14, rbp
	xor r14, r9
	add r10, r14
	add rbx, r10
	mov r14, r11
	ror r14, 28
	mov r15, r11
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r10, r14
	mov r14, r11
	or r14, r12
	and r14, rax
	mov r15, r11
	and r15, r12
	or r14, r15
	add r10, r14
	mov r13, QWORD PTR [rdx+88]
	bswap r13
	mov QWORD PTR [rcx+88], r13
	add r9, QWORD PTR [rsi+88]
	add r9, r13
	mov r14, rbx
	ror r14, 14
	mov r15, rbx
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r9, r14
	mov r14, rbp
	xor r14, r8
	and r14, rbx
	xor r14, r8
	add r9, r14
	add rax, r9
	mov r14, r10
	ror r14, 28
	mov r15, r10
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r9, r14
	mov r14, r10
	or r14, r11
	and r14, r12
	mov r15, r10
	and r15, r11
	or r14, r15
	add r9, r14
	mov r13, QWORD PTR [rdx+96]
	bswap r13
	mov QWORD PTR [rcx+96], r13
	add r8, QWORD PTR [rsi+96]
	add r8, r13
	mov r14, rax
	ror r14, 14
	mov r15, rax
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r8, r14
	mov r14, rbx
	xor r14, rbp
	and r14, rax
	xor r14, rbp
	add r8, r14
	add r12, r8
	mov r14, r9
	ror r14, 28
	mov r15, r9
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r8, r14
	mov r14, r9
	or r14, r10
	and r14, r11
	mov r15, r9
	and r15, r10
	or r14, r15
	add r8, r14
	mov r13, QWORD PTR [rdx+104]
	bswap r13
	mov QWORD PTR [rcx+104], r13
	add rbp, QWORD PTR [rsi+104]
	add rbp, r13
	mov r14, r12
	ror r14, 14
	mov r15, r12
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add rbp, r14
	mov r14, rax
	xor r14, rbx
	and r14, r12
	xor r14, rbx
	add rbp, r14
	add r11, rbp
	mov r14, r8
	ror r14, 28
	mov r15, r8
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add rbp, r14
	mov r14, r8
	or r14, r9
	and r14, r10
	mov r15, r8
	and r15, r9
	or r14, r15
	add rbp, r14
	mov r13, QWORD PTR [rdx+112]
	bswap r13
	mov QWORD PTR [rcx+112], r13
	add rbx, QWORD PTR [rsi+112]
	add rbx, r13
	mov r14, r11
	ror r14, 14
	mov r15, r11
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add rbx, r14
	mov r14, r12
	xor r14, rax
	and r14, r11
	xor r14, rax
	add rbx, r14
	add r10, rbx
	mov r14, rbp
	ror r14, 28
	mov r15, rbp
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add rbx, r14
	mov r14, rbp
	or r14, r8
	and r14, r9
	mov r15, rbp
	and r15, r8
	or r14, r15
	add rbx, r14
	mov r13, QWORD PTR [rdx+120]
	bswap r13
	mov QWORD PTR [rcx+120], r13
	add rax, QWORD PTR [rsi+120]
	add rax, r13
	mov r14, r10
	ror r14, 14
	mov r15, r10
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add rax, r14
	mov r14, r11
	xor r14, r12
	and r14, r10
	xor r14, r12
	add rax, r14
	add r9, rax
	mov r14, rbx
	ror r14, 28
	mov r15, rbx
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add rax, r14
	mov r14, rbx
	or r14, rbp
	and r14, r8
	mov r15, rbx
	and r15, rbp
	or r14, r15
	add rax, r14
	mov rdx, 128
23:
	mov r14, QWORD PTR [rcx+112]
	mov r13, r14
	ror r13, 42
	xor r13, r14
	ror r13, 19
	shr r14, 6
	xor r13, r14
	add r13, QWORD PTR [rcx+72]
	mov r14, QWORD PTR [rcx+8]
	mov r15, r14
	ror r15, 7
	xor r15, r14
	ror r15, 1
	shr r14, 7
	xor r15, r14
	add r13, r15
	add r13, QWORD PTR [rcx]
	mov QWORD PTR [rcx], r13
	add r12, QWORD PTR [rsi+rdx*1]
	add r12, r13
	mov r14, r9
	ror r14, 14
	mov r15, r9
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r12, r14
	mov r14, r10
	xor r14, r11
	and r14, r9
	xor r14, r11
	add r12, r14
	add r8, r12
	mov r14, rax
	ror r14, 28
	mov r15, rax
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r12, r14
	mov r14, rax
	or r14, rbx
	and r14, rbp
	mov r15, rax
	and r15, rbx
	or r14, r15
	add r12, r14
	mov r14, QWORD PTR [rcx+120]
	mov r13, r14
	ror r13, 42
	xor r13, r14
	ror r13, 19
	shr r14, 6
	xor r13, r14
	add r13, QWORD PTR [rcx+80]
	mov r14, QWORD PTR [rcx+16]
	mov r15, r14
	ror r15, 7
	xor r15, r14
	ror r15, 1
	shr r14, 7
	xor r15, r14
	add r13, r15
	add r13, QWORD PTR [rcx+8]
	mov QWORD PTR [rcx+8], r13
	add r11, QWORD PTR [rsi+rdx*1+8]
	add r11, r13
	mov r14, r8
	ror r14, 14
	mov r15, r8
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r11, r14
	mov r14, r9
	xor r14, r10
	and r14, r8
	xor r14, r10
	add r11, r14
	add rbp, r11
	mov r14, r12
	ror r14, 28
	mov r15, r12
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r11, r14
	mov r14, r12
	or r14, rax
	and r14, rbx
	mov r15, r12
	and r15, rax
	or r14, r15
	add r11, r14
	mov r14, QWORD PTR [rcx]
	mov r13, r14
	ror r13, 42
	xor r13, r14
	ror r13, 19
	shr r14, 6
	xor r13, r14
	add r13, QWORD PTR [rcx+88]
	mov r14, QWORD PTR [rcx+24]
	mov r15, r14
	ror r15, 7
	xor r15, r14
	ror r15, 1
	shr r14, 7
	xor r15, r14
	add r13, r15
	add r13, QWORD PTR [rcx+16]
	mov QWORD PTR [rcx+16], r13
	add r10, QWORD PTR [rsi+rdx*1+16]
	add r10, r13
	mov r14, rbp
	ror r14, 14
	mov r15, rbp
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r10, r14
	mov r14, r8
	xor r14, r9
	and r14, rbp
	xor r14, r9
	add r10, r14
	add rbx, r10
	mov r14, r11
	ror r14, 28
	mov r15, r11
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r10, r14
	mov r14, r11
	or r14, r12
	and r14, rax
	mov r15, r11
	and r15, r12
	or r14, r15
	add r10, r14
	mov r14, QWORD PTR [rcx+8]
	mov r13, r14
	ror r13, 42
	xor r13, r14
	ror r13, 19
	shr r14, 6
	xor r13, r14
	add r13, QWORD PTR [rcx+96]
	mov r14, QWORD PTR [rcx+32]
	mov r15, r14
	ror r15, 7
	xor r15, r14
	ror r15, 1
	shr r14, 7
	xor r15, r14
	add r13, r15
	add r13, QWORD PTR [rcx+24]
	mov QWORD PTR [rcx+24], r13
	add r9, QWORD PTR [rsi+rdx*1+24]
	add r9, r13
	mov r14, rbx
	ror r14, 14
	mov r15, rbx
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r9, r14
	mov r14, rbp
	xor r14, r8
	and r14, rbx
	xor r14, r8
	add r9, r14
	add rax, r9
	mov r14, r10
	ror r14, 28
	mov r15, r10
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r9, r14
	mov r14, r10
	or r14, r11
	and r14, r12
	mov r15, r10
	and r15, r11
	or r14, r15
	add r9, r14
	mov r14, QWORD PTR [rcx+16]
	mov r13, r14
	ror r13, 42
	xor r13, r14
	ror r13, 19
	shr r14, 6
	xor r13, r14
	add r13, QWORD PTR [rcx+104]
	mov r14, QWORD PTR [rcx+40]
	mov r15, r14
	ror r15, 7
	xor r15, r14
	ror r15, 1
	shr r14, 7
	xor r15, r14
	add r13, r15
	add r13, QWORD PTR [rcx+32]
	mov QWORD PTR [rcx+32], r13
	add r8, QWORD PTR [rsi+rdx*1+32]
	add r8, r13
	mov r14, rax
	ror r14, 14
	mov r15, rax
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r8, r14
	mov r14, rbx
	xor r14, rbp
	and r14, rax
	xor r14, rbp
	add r8, r14
	add r12, r8
	mov r14, r9
	ror r14, 28
	mov r15, r9
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r8, r14
	mov r14, r9
	or r14, r10
	and r14, r11
	mov r15, r9
	and r15, r10
	or r14, r15
	add r8, r14
	mov r14, QWORD PTR [rcx+24]
	mov r13, r14
	ror r13, 42
	xor r13, r14
	ror r13, 19
	shr r14, 6
	xor r13, r14
	add r13, QWORD PTR [rcx+112]
	mov r14, QWORD PTR [rcx+48]
	mov r15, r14
	ror r15, 7
	xor r15, r14
	ror r15, 1
	shr r14, 7
	xor r15, r14
	add r13, r15
	add r13, QWORD PTR [rcx+40]
	mov QWORD PTR [rcx+40], r13
	add rbp, QWORD PTR [rsi+rdx*1+40]
	add rbp, r13
	mov r14, r12
	ror r14, 14
	mov r15, r12
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add rbp, r14
	mov r14, rax
	xor r14, rbx
	and r14, r12
	xor r14, rbx
	add rbp, r14
	add r11, rbp
	mov r14, r8
	ror r14, 28
	mov r15, r8
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add rbp, r14
	mov r14, r8
	or r14, r9
	and r14, r10
	mov r15, r8
	and r15, r9
	or r14, r15
	add rbp, r14
	mov r14, QWORD PTR [rcx+32]
	mov r13, r14
	ror r13, 42
	xor r13, r14
	ror r13, 19
	shr r14, 6
	xor r13, r14
	add r13, QWORD PTR [rcx+120]
	mov r14, QWORD PTR [rcx+56]
	mov r15, r14
	ror r15, 7
	xor r15, r14
	ror r15, 1
	shr r14, 7
	xor r15, r14
	add r13, r15
	add r13, QWORD PTR [rcx+48]
	mov QWORD PTR [rcx+48], r13
	add rbx, QWORD PTR [rsi+rdx*1+48]
	add rbx, r13
	mov r14, r11
	ror r14, 14
	mov r15, r11
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add rbx, r14
	mov r14, r12
	xor r14, rax
	and r14, r11
	xor r14, rax
	add rbx, r14
	add r10, rbx
	mov r14, rbp
	ror r14, 28
	mov r15, rbp
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add rbx, r14
	mov r14, rbp
	or r14, r8
	and r14, r9
	mov r15, rbp
	and r15, r8
	or r14, r15
	add rbx, r14
	mov r14, QWORD PTR [rcx+40]
	mov r13, r14
	ror r13, 42
	xor r13, r14
	ror r13, 19
	shr r14, 6
	xor r13, r14
	add r13, QWORD PTR [rcx]
	mov r14, QWORD PTR [rcx+64]
	mov r15, r14
	ror r15, 7
	xor r15, r14
	ror r15, 1
	shr r14, 7
	xor r15, r14
	add r13, r15
	add r13, QWORD PTR [rcx+56]
	mov QWORD PTR [rcx+56], r13
	add rax, QWORD PTR [rsi+rdx*1+56]
	add rax, r13
	mov r14, r10
	ror r14, 14
	mov r15, r10
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add rax, r14
	mov r14, r11
	xor r14, r12
	and r14, r10
	xor r14, r12
	add rax, r14
	add r9, rax
	mov r14, rbx
	ror r14, 28
	mov r15, rbx
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add rax, r14
	mov r14, rbx
	or r14, rbp
	and r14, r8
	mov r15, rbx
	and r15, rbp
	or r14, r15
	add rax, r14
	mov r14, QWORD PTR [rcx+48]
	mov r13, r14
	ror r13, 42
	xor r13, r14
	ror r13, 19
	shr r14, 6
	xor r13, r14
	add r13, QWORD PTR [rcx+8]
	mov r14, QWORD PTR [rcx+72]
	mov r15, r14
	ror r15, 7
	xor r15, r14
	ror r15, 1
	shr r14, 7
	xor r15, r14
	add r13, r15
	add r13, QWORD PTR [rcx+64]
	mov QWORD PTR [rcx+64], r13
	add r12, QWORD PTR [rsi+rdx*1+64]
	add r12, r13
	mov r14, r9
	ror r14, 14
	mov r15, r9
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r12, r14
	mov r14, r10
	xor r14, r11
	and r14, r9
	xor r14, r11
	add r12, r14
	add r8, r12
	mov r14, rax
	ror r14, 28
	mov r15, rax
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r12, r14
	mov r14, rax
	or r14, rbx
	and r14, rbp
	mov r15, rax
	and r15, rbx
	or r14, r15
	add r12, r14
	mov r14, QWORD PTR [rcx+56]
	mov r13, r14
	ror r13, 42
	xor r13, r14
	ror r13, 19
	shr r14, 6
	xor r13, r14
	add r13, QWORD PTR [rcx+16]
	mov r14, QWORD PTR [rcx+80]
	mov r15, r14
	ror r15, 7
	xor r15, r14
	ror r15, 1
	shr r14, 7
	xor r15, r14
	add r13, r15
	add r13, QWORD PTR [rcx+72]
	mov QWORD PTR [rcx+72], r13
	add r11, QWORD PTR [rsi+rdx*1+72]
	add r11, r13
	mov r14, r8
	ror r14, 14
	mov r15, r8
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r11, r14
	mov r14, r9
	xor r14, r10
	and r14, r8
	xor r14, r10
	add r11, r14
	add rbp, r11
	mov r14, r12
	ror r14, 28
	mov r15, r12
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r11, r14
	mov r14, r12
	or r14, rax
	and r14, rbx
	mov r15, r12
	and r15, rax
	or r14, r15
	add r11, r14
	mov r14, QWORD PTR [rcx+64]
	mov r13, r14
	ror r13, 42
	xor r13, r14
	ror r13, 19
	shr r14, 6
	xor r13, r14
	add r13, QWORD PTR [rcx+24]
	mov r14, QWORD PTR [rcx+88]
	mov r15, r14
	ror r15, 7
	xor r15, r14
	ror r15, 1
	shr r14, 7
	xor r15, r14
	add r13, r15
	add r13, QWORD PTR [rcx+80]
	mov QWORD PTR [rcx+80], r13
	add r10, QWORD PTR [rsi+rdx*1+80]
	add r10, r13
	mov r14, rbp
	ror r14, 14
	mov r15, rbp
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r10, r14
	mov r14, r8
	xor r14, r9
	and r14, rbp
	xor r14, r9
	add r10, r14
	add rbx, r10
	mov r14, r11
	ror r14, 28
	mov r15, r11
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r10, r14
	mov r14, r11
	or r14, r12
	and r14, rax
	mov r15, r11
	and r15, r12
	or r14, r15
	add r10, r14
	mov r14, QWORD PTR [rcx+72]
	mov r13, r14
	ror r13, 42
	xor r13, r14
	ror r13, 19
	shr r14, 6
	xor r13, r14
	add r13, QWORD PTR [rcx+32]
	mov r14, QWORD PTR [rcx+96]
	mov r15, r14
	ror r15, 7
	xor r15, r14
	ror r15, 1
	shr r14, 7
	xor r15, r14
	add r13, r15
	add r13, QWORD PTR [rcx+88]
	mov QWORD PTR [rcx+88], r13
	add r9, QWORD PTR [rsi+rdx*1+88]
	add r9, r13
	mov r14, rbx
	ror r14, 14
	mov r15, rbx
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r9, r14
	mov r14, rbp
	xor r14, r8
	and r14, rbx
	xor r14, r8
	add r9, r14
	add rax, r9
	mov r14, r10
	ror r14, 28
	mov r15, r10
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r9, r14
	mov r14, r10
	or r14, r11
	and r14, r12
	mov r15, r10
	and r15, r11
	or r14, r15
	add r9, r14
	mov r14, QWORD PTR [rcx+80]
	mov r13, r14
	ror r13, 42
	xor r13, r14
	ror r13, 19
	shr r14, 6
	xor r13, r14
	add r13, QWORD PTR [rcx+40]
	mov r14, QWORD PTR [rcx+104]
	mov r15, r14
	ror r15, 7
	xor r15, r14
	ror r15, 1
	shr r14, 7
	xor r15, r14
	add r13, r15
	add r13, QWORD PTR [rcx+96]
	mov QWORD PTR [rcx+96], r13
	add r8, QWORD PTR [rsi+rdx*1+96]
	add r8, r13
	mov r14, rax
	ror r14, 14
	mov r15, rax
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add r8, r14
	mov r14, rbx
	xor r14, rbp
	and r14, rax
	xor r14, rbp
	add r8, r14
	add r12, r8
	mov r14, r9
	ror r14, 28
	mov r15, r9
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add r8, r14
	mov r14, r9
	or r14, r10
	and r14, r11
	mov r15, r9
	and r15, r10
	or r14, r15
	add r8, r14
	mov r14, QWORD PTR [rcx+88]
	mov r13, r14
	ror r13, 42
	xor r13, r14
	ror r13, 19
	shr r14, 6
	xor r13, r14
	add r13, QWORD PTR [rcx+48]
	mov r14, QWORD PTR [rcx+112]
	mov r15, r14
	ror r15, 7
	xor r15, r14
	ror r15, 1
	shr r14, 7
	xor r15, r14
	add r13, r15
	add r13, QWORD PTR [rcx+104]
	mov QWORD PTR [rcx+104], r13
	add rbp, QWORD PTR [rsi+rdx*1+104]
	add rbp, r13
	mov r14, r12
	ror r14, 14
	mov r15, r12
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add rbp, r14
	mov r14, rax
	xor r14, rbx
	and r14, r12
	xor r14, rbx
	add rbp, r14
	add r11, rbp
	mov r14, r8
	ror r14, 28
	mov r15, r8
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add rbp, r14
	mov r14, r8
	or r14, r9
	and r14, r10
	mov r15, r8
	and r15, r9
	or r14, r15
	add rbp, r14
	mov r14, QWORD PTR [rcx+96]
	mov r13, r14
	ror r13, 42
	xor r13, r14
	ror r13, 19
	shr r14, 6
	xor r13, r14
	add r13, QWORD PTR [rcx+56]
	mov r14, QWORD PTR [rcx+120]
	mov r15, r14
	ror r15, 7
	xor r15, r14
	ror r15, 1
	shr r14, 7
	xor r15, r14
	add r13, r15
	add r13, QWORD PTR [rcx+112]
	mov QWORD PTR [rcx+112], r13
	add rbx, QWORD PTR [rsi+rdx*1+112]
	add rbx, r13
	mov r14, r11
	ror r14, 14
	mov r15, r11
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add rbx, r14
	mov r14, r12
	xor r14, rax
	and r14, r11
	xor r14, rax
	add rbx, r14
	add r10, rbx
	mov r14, rbp
	ror r14, 28
	mov r15, rbp
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add rbx, r14
	mov r14, rbp
	or r14, r8
	and r14, r9
	mov r15, rbp
	and r15, r8
	or r14, r15
	add rbx, r14
	mov r14, QWORD PTR [rcx+104]
	mov r13, r14
	ror r13, 42
	xor r13, r14
	ror r13, 19
	shr r14, 6
	xor r13, r14
	add r13, QWORD PTR [rcx+64]
	mov r14, QWORD PTR [rcx]
	mov r15, r14
	ror r15, 7
	xor r15, r14
	ror r15, 1
	shr r14, 7
	xor r15, r14
	add r13, r15
	add r13, QWORD PTR [rcx+120]
	mov QWORD PTR [rcx+120], r13
	add rax, QWORD PTR [rsi+rdx*1+120]
	add rax, r13
	mov r14, r10
	ror r14, 14
	mov r15, r10
	ror r15, 18
	xor r14, r15
	ror r15, 23
	xor r14, r15
	add rax, r14
	mov r14, r11
	xor r14, r12
	and r14, r10
	xor r14, r12
	add rax, r14
	add r9, rax
	mov r14, rbx
	ror r14, 28
	mov r15, rbx
	ror r15, 34
	xor r14, r15
	ror r15, 5
	xor r14, r15
	add rax, r14
	mov r14, rbx
	or r14, rbp
	and r14, r8
	mov r15, rbx
	and r15, rbp
	or r14, r15
	add rax, r14
	add rdx, 128
	cmp rdx, 640
	jne 23b
	mov rsi, QWORD PTR [rcx+176]
	mov rdx, QWORD PTR [rcx+184]
	add rax, QWORD PTR [rdi]
	add rbx, QWORD PTR [rdi+8]
	add rbp, QWORD PTR [rdi+16]
	add r8, QWORD PTR [rdi+24]
	add r9, QWORD PTR [rdi+32]
	add r10, QWORD PTR [rdi+40]
	add r11, QWORD PTR [rdi+48]
	add r12, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], rbp
	mov QWORD PTR [rdi+24], r8
	mov QWORD PTR [rdi+32], r9
	mov QWORD PTR [rdi+40], r10
	mov QWORD PTR [rdi+48], r11
	mov QWORD PTR [rdi+56], r12
	add rsi, 128
	sub rdx, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [rcx+128]
	mov rbp, QWORD PTR [rcx+136]
	mov r12, QWORD PTR [rcx+144]
	mov r13, QWORD PTR [rcx+152]
	mov r14, QWORD PTR [rcx+160]
	mov r15, QWORD PTR [rcx+168]
	ret
	.p2align 6

vg_sha512_compress_avx2:
	mov QWORD PTR [rcx+1280], rbx
	mov QWORD PTR [rcx+1288], rbp
	mov QWORD PTR [rcx+1296], r12
	mov QWORD PTR [rcx+1304], r13
	vmovq xmm14, r14
	vmovq xmm15, r15
	movabs rax, 283686952306183
	vmovq xmm12, rax
	movabs rax, 579005069656919567
	vmovq xmm13, rax
	vpunpcklqdq xmm12, xmm12, xmm13
	vinserti128 ymm12, ymm12, xmm12, 1
	test rdx, rdx
	je 20f
22:
	mov r15, rsi
	cmp rdx, 1
	je 23f
	add r15, 128
	jmp 24f
23:
24:
	vmovdqu xmm0, XMMWORD PTR [rsi]
	vmovdqu xmm13, XMMWORD PTR [r15]
	vinserti128 ymm0, ymm0, xmm13, 1
	vpshufb ymm0, ymm0, ymm12
	vmovdqu YMMWORD PTR [rcx], ymm0
	vmovdqu xmm1, XMMWORD PTR [rsi+16]
	vmovdqu xmm13, XMMWORD PTR [r15+16]
	vinserti128 ymm1, ymm1, xmm13, 1
	vpshufb ymm1, ymm1, ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm1
	vmovdqu xmm2, XMMWORD PTR [rsi+32]
	vmovdqu xmm13, XMMWORD PTR [r15+32]
	vinserti128 ymm2, ymm2, xmm13, 1
	vpshufb ymm2, ymm2, ymm12
	vmovdqu YMMWORD PTR [rcx+64], ymm2
	vmovdqu xmm3, XMMWORD PTR [rsi+48]
	vmovdqu xmm13, XMMWORD PTR [r15+48]
	vinserti128 ymm3, ymm3, xmm13, 1
	vpshufb ymm3, ymm3, ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm3
	vmovdqu xmm4, XMMWORD PTR [rsi+64]
	vmovdqu xmm13, XMMWORD PTR [r15+64]
	vinserti128 ymm4, ymm4, xmm13, 1
	vpshufb ymm4, ymm4, ymm12
	vmovdqu YMMWORD PTR [rcx+128], ymm4
	vmovdqu xmm5, XMMWORD PTR [rsi+80]
	vmovdqu xmm13, XMMWORD PTR [r15+80]
	vinserti128 ymm5, ymm5, xmm13, 1
	vpshufb ymm5, ymm5, ymm12
	vmovdqu YMMWORD PTR [rcx+160], ymm5
	vmovdqu xmm6, XMMWORD PTR [rsi+96]
	vmovdqu xmm13, XMMWORD PTR [r15+96]
	vinserti128 ymm6, ymm6, xmm13, 1
	vpshufb ymm6, ymm6, ymm12
	vmovdqu YMMWORD PTR [rcx+192], ymm6
	vmovdqu xmm7, XMMWORD PTR [rsi+112]
	vmovdqu xmm13, XMMWORD PTR [r15+112]
	vinserti128 ymm7, ymm7, xmm13, 1
	vpshufb ymm7, ymm7, ymm12
	vmovdqu YMMWORD PTR [rcx+224], ymm7
	mov rax, QWORD PTR [rdi]
	mov rbx, QWORD PTR [rdi+8]
	mov rbp, QWORD PTR [rdi+16]
	mov r8, QWORD PTR [rdi+24]
	mov r9, QWORD PTR [rdi+32]
	mov r10, QWORD PTR [rdi+40]
	mov r11, QWORD PTR [rdi+48]
	mov r12, QWORD PTR [rdi+56]
	mov r13, rbx
	xor r13, rbp
	mov QWORD PTR [rcx+1312], rsi
	mov QWORD PTR [rcx+1320], rdx
	lea rsi, {VG_SHA512_K}
	mov rdx, 0
25:
	vpalignr ymm8, ymm1, ymm0, 8
	add r12, QWORD PTR [rsi+rdx*1]
	add r12, QWORD PTR [rcx+rdx*2]
	mov r14, r9
	vpalignr ymm9, ymm5, ymm4, 8
	and r14, r10
	andn r15, r9, r11
	vpaddq ymm0, ymm0, ymm9
	add r14, r15
	add r12, r14
	vpsrlq ymm10, ymm8, 1
	rorx r14, r9, 14
	rorx r15, r9, 18
	vpsllq ymm11, ymm8, 63
	xor r14, r15
	rorx r15, r9, 41
	vpxor ymm10, ymm10, ymm11
	xor r14, r15
	add r12, r14
	vpsrlq ymm11, ymm8, 8
	add r8, r12
	rorx r14, rax, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, rax, 34
	xor r14, r15
	vpsllq ymm11, ymm8, 56
	rorx r15, rax, 39
	xor r14, r15
	vpxor ymm10, ymm10, ymm11
	add r12, r14
	mov r14, rax
	vpsrlq ymm11, ymm8, 7
	xor r14, rbx
	and r13, r14
	vpxor ymm10, ymm10, ymm11
	xor r13, rbx
	add r12, r13
	vpaddq ymm0, ymm0, ymm10
	add r11, QWORD PTR [rsi+rdx*1+8]
	add r11, QWORD PTR [rcx+rdx*2+8]
	mov r13, r8
	vpsrlq ymm10, ymm7, 19
	and r13, r9
	andn r15, r8, r10
	vpsllq ymm11, ymm7, 45
	add r13, r15
	add r11, r13
	vpxor ymm10, ymm10, ymm11
	rorx r13, r8, 14
	rorx r15, r8, 18
	vpsrlq ymm11, ymm7, 61
	xor r13, r15
	rorx r15, r8, 41
	vpxor ymm10, ymm10, ymm11
	xor r13, r15
	add r11, r13
	vpsllq ymm11, ymm7, 3
	add rbp, r11
	rorx r13, r12, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r12, 34
	xor r13, r15
	vpsrlq ymm11, ymm7, 6
	rorx r15, r12, 39
	xor r13, r15
	vpxor ymm10, ymm10, ymm11
	add r11, r13
	mov r13, r12
	vpaddq ymm0, ymm0, ymm10
	xor r13, rax
	and r14, r13
	vmovdqu YMMWORD PTR [rcx+rdx*2+256], ymm0
	xor r14, rax
	add r11, r14
	vpalignr ymm8, ymm2, ymm1, 8
	add r10, QWORD PTR [rsi+rdx*1+16]
	add r10, QWORD PTR [rcx+rdx*2+32]
	mov r14, rbp
	vpalignr ymm9, ymm6, ymm5, 8
	and r14, r8
	andn r15, rbp, r9
	vpaddq ymm1, ymm1, ymm9
	add r14, r15
	add r10, r14
	vpsrlq ymm10, ymm8, 1
	rorx r14, rbp, 14
	rorx r15, rbp, 18
	vpsllq ymm11, ymm8, 63
	xor r14, r15
	rorx r15, rbp, 41
	vpxor ymm10, ymm10, ymm11
	xor r14, r15
	add r10, r14
	vpsrlq ymm11, ymm8, 8
	add rbx, r10
	rorx r14, r11, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r11, 34
	xor r14, r15
	vpsllq ymm11, ymm8, 56
	rorx r15, r11, 39
	xor r14, r15
	vpxor ymm10, ymm10, ymm11
	add r10, r14
	mov r14, r11
	vpsrlq ymm11, ymm8, 7
	xor r14, r12
	and r13, r14
	vpxor ymm10, ymm10, ymm11
	xor r13, r12
	add r10, r13
	vpaddq ymm1, ymm1, ymm10
	add r9, QWORD PTR [rsi+rdx*1+24]
	add r9, QWORD PTR [rcx+rdx*2+40]
	mov r13, rbx
	vpsrlq ymm10, ymm0, 19
	and r13, rbp
	andn r15, rbx, r8
	vpsllq ymm11, ymm0, 45
	add r13, r15
	add r9, r13
	vpxor ymm10, ymm10, ymm11
	rorx r13, rbx, 14
	rorx r15, rbx, 18
	vpsrlq ymm11, ymm0, 61
	xor r13, r15
	rorx r15, rbx, 41
	vpxor ymm10, ymm10, ymm11
	xor r13, r15
	add r9, r13
	vpsllq ymm11, ymm0, 3
	add rax, r9
	rorx r13, r10, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r10, 34
	xor r13, r15
	vpsrlq ymm11, ymm0, 6
	rorx r15, r10, 39
	xor r13, r15
	vpxor ymm10, ymm10, ymm11
	add r9, r13
	mov r13, r10
	vpaddq ymm1, ymm1, ymm10
	xor r13, r11
	and r14, r13
	vmovdqu YMMWORD PTR [rcx+rdx*2+288], ymm1
	xor r14, r11
	add r9, r14
	vpalignr ymm8, ymm3, ymm2, 8
	add r8, QWORD PTR [rsi+rdx*1+32]
	add r8, QWORD PTR [rcx+rdx*2+64]
	mov r14, rax
	vpalignr ymm9, ymm7, ymm6, 8
	and r14, rbx
	andn r15, rax, rbp
	vpaddq ymm2, ymm2, ymm9
	add r14, r15
	add r8, r14
	vpsrlq ymm10, ymm8, 1
	rorx r14, rax, 14
	rorx r15, rax, 18
	vpsllq ymm11, ymm8, 63
	xor r14, r15
	rorx r15, rax, 41
	vpxor ymm10, ymm10, ymm11
	xor r14, r15
	add r8, r14
	vpsrlq ymm11, ymm8, 8
	add r12, r8
	rorx r14, r9, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r9, 34
	xor r14, r15
	vpsllq ymm11, ymm8, 56
	rorx r15, r9, 39
	xor r14, r15
	vpxor ymm10, ymm10, ymm11
	add r8, r14
	mov r14, r9
	vpsrlq ymm11, ymm8, 7
	xor r14, r10
	and r13, r14
	vpxor ymm10, ymm10, ymm11
	xor r13, r10
	add r8, r13
	vpaddq ymm2, ymm2, ymm10
	add rbp, QWORD PTR [rsi+rdx*1+40]
	add rbp, QWORD PTR [rcx+rdx*2+72]
	mov r13, r12
	vpsrlq ymm10, ymm1, 19
	and r13, rax
	andn r15, r12, rbx
	vpsllq ymm11, ymm1, 45
	add r13, r15
	add rbp, r13
	vpxor ymm10, ymm10, ymm11
	rorx r13, r12, 14
	rorx r15, r12, 18
	vpsrlq ymm11, ymm1, 61
	xor r13, r15
	rorx r15, r12, 41
	vpxor ymm10, ymm10, ymm11
	xor r13, r15
	add rbp, r13
	vpsllq ymm11, ymm1, 3
	add r11, rbp
	rorx r13, r8, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r8, 34
	xor r13, r15
	vpsrlq ymm11, ymm1, 6
	rorx r15, r8, 39
	xor r13, r15
	vpxor ymm10, ymm10, ymm11
	add rbp, r13
	mov r13, r8
	vpaddq ymm2, ymm2, ymm10
	xor r13, r9
	and r14, r13
	vmovdqu YMMWORD PTR [rcx+rdx*2+320], ymm2
	xor r14, r9
	add rbp, r14
	vpalignr ymm8, ymm4, ymm3, 8
	add rbx, QWORD PTR [rsi+rdx*1+48]
	add rbx, QWORD PTR [rcx+rdx*2+96]
	mov r14, r11
	vpalignr ymm9, ymm0, ymm7, 8
	and r14, r12
	andn r15, r11, rax
	vpaddq ymm3, ymm3, ymm9
	add r14, r15
	add rbx, r14
	vpsrlq ymm10, ymm8, 1
	rorx r14, r11, 14
	rorx r15, r11, 18
	vpsllq ymm11, ymm8, 63
	xor r14, r15
	rorx r15, r11, 41
	vpxor ymm10, ymm10, ymm11
	xor r14, r15
	add rbx, r14
	vpsrlq ymm11, ymm8, 8
	add r10, rbx
	rorx r14, rbp, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, rbp, 34
	xor r14, r15
	vpsllq ymm11, ymm8, 56
	rorx r15, rbp, 39
	xor r14, r15
	vpxor ymm10, ymm10, ymm11
	add rbx, r14
	mov r14, rbp
	vpsrlq ymm11, ymm8, 7
	xor r14, r8
	and r13, r14
	vpxor ymm10, ymm10, ymm11
	xor r13, r8
	add rbx, r13
	vpaddq ymm3, ymm3, ymm10
	add rax, QWORD PTR [rsi+rdx*1+56]
	add rax, QWORD PTR [rcx+rdx*2+104]
	mov r13, r10
	vpsrlq ymm10, ymm2, 19
	and r13, r11
	andn r15, r10, r12
	vpsllq ymm11, ymm2, 45
	add r13, r15
	add rax, r13
	vpxor ymm10, ymm10, ymm11
	rorx r13, r10, 14
	rorx r15, r10, 18
	vpsrlq ymm11, ymm2, 61
	xor r13, r15
	rorx r15, r10, 41
	vpxor ymm10, ymm10, ymm11
	xor r13, r15
	add rax, r13
	vpsllq ymm11, ymm2, 3
	add r9, rax
	rorx r13, rbx, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, rbx, 34
	xor r13, r15
	vpsrlq ymm11, ymm2, 6
	rorx r15, rbx, 39
	xor r13, r15
	vpxor ymm10, ymm10, ymm11
	add rax, r13
	mov r13, rbx
	vpaddq ymm3, ymm3, ymm10
	xor r13, rbp
	and r14, r13
	vmovdqu YMMWORD PTR [rcx+rdx*2+352], ymm3
	xor r14, rbp
	add rax, r14
	vpalignr ymm8, ymm5, ymm4, 8
	add r12, QWORD PTR [rsi+rdx*1+64]
	add r12, QWORD PTR [rcx+rdx*2+128]
	mov r14, r9
	vpalignr ymm9, ymm1, ymm0, 8
	and r14, r10
	andn r15, r9, r11
	vpaddq ymm4, ymm4, ymm9
	add r14, r15
	add r12, r14
	vpsrlq ymm10, ymm8, 1
	rorx r14, r9, 14
	rorx r15, r9, 18
	vpsllq ymm11, ymm8, 63
	xor r14, r15
	rorx r15, r9, 41
	vpxor ymm10, ymm10, ymm11
	xor r14, r15
	add r12, r14
	vpsrlq ymm11, ymm8, 8
	add r8, r12
	rorx r14, rax, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, rax, 34
	xor r14, r15
	vpsllq ymm11, ymm8, 56
	rorx r15, rax, 39
	xor r14, r15
	vpxor ymm10, ymm10, ymm11
	add r12, r14
	mov r14, rax
	vpsrlq ymm11, ymm8, 7
	xor r14, rbx
	and r13, r14
	vpxor ymm10, ymm10, ymm11
	xor r13, rbx
	add r12, r13
	vpaddq ymm4, ymm4, ymm10
	add r11, QWORD PTR [rsi+rdx*1+72]
	add r11, QWORD PTR [rcx+rdx*2+136]
	mov r13, r8
	vpsrlq ymm10, ymm3, 19
	and r13, r9
	andn r15, r8, r10
	vpsllq ymm11, ymm3, 45
	add r13, r15
	add r11, r13
	vpxor ymm10, ymm10, ymm11
	rorx r13, r8, 14
	rorx r15, r8, 18
	vpsrlq ymm11, ymm3, 61
	xor r13, r15
	rorx r15, r8, 41
	vpxor ymm10, ymm10, ymm11
	xor r13, r15
	add r11, r13
	vpsllq ymm11, ymm3, 3
	add rbp, r11
	rorx r13, r12, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r12, 34
	xor r13, r15
	vpsrlq ymm11, ymm3, 6
	rorx r15, r12, 39
	xor r13, r15
	vpxor ymm10, ymm10, ymm11
	add r11, r13
	mov r13, r12
	vpaddq ymm4, ymm4, ymm10
	xor r13, rax
	and r14, r13
	vmovdqu YMMWORD PTR [rcx+rdx*2+384], ymm4
	xor r14, rax
	add r11, r14
	vpalignr ymm8, ymm6, ymm5, 8
	add r10, QWORD PTR [rsi+rdx*1+80]
	add r10, QWORD PTR [rcx+rdx*2+160]
	mov r14, rbp
	vpalignr ymm9, ymm2, ymm1, 8
	and r14, r8
	andn r15, rbp, r9
	vpaddq ymm5, ymm5, ymm9
	add r14, r15
	add r10, r14
	vpsrlq ymm10, ymm8, 1
	rorx r14, rbp, 14
	rorx r15, rbp, 18
	vpsllq ymm11, ymm8, 63
	xor r14, r15
	rorx r15, rbp, 41
	vpxor ymm10, ymm10, ymm11
	xor r14, r15
	add r10, r14
	vpsrlq ymm11, ymm8, 8
	add rbx, r10
	rorx r14, r11, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r11, 34
	xor r14, r15
	vpsllq ymm11, ymm8, 56
	rorx r15, r11, 39
	xor r14, r15
	vpxor ymm10, ymm10, ymm11
	add r10, r14
	mov r14, r11
	vpsrlq ymm11, ymm8, 7
	xor r14, r12
	and r13, r14
	vpxor ymm10, ymm10, ymm11
	xor r13, r12
	add r10, r13
	vpaddq ymm5, ymm5, ymm10
	add r9, QWORD PTR [rsi+rdx*1+88]
	add r9, QWORD PTR [rcx+rdx*2+168]
	mov r13, rbx
	vpsrlq ymm10, ymm4, 19
	and r13, rbp
	andn r15, rbx, r8
	vpsllq ymm11, ymm4, 45
	add r13, r15
	add r9, r13
	vpxor ymm10, ymm10, ymm11
	rorx r13, rbx, 14
	rorx r15, rbx, 18
	vpsrlq ymm11, ymm4, 61
	xor r13, r15
	rorx r15, rbx, 41
	vpxor ymm10, ymm10, ymm11
	xor r13, r15
	add r9, r13
	vpsllq ymm11, ymm4, 3
	add rax, r9
	rorx r13, r10, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r10, 34
	xor r13, r15
	vpsrlq ymm11, ymm4, 6
	rorx r15, r10, 39
	xor r13, r15
	vpxor ymm10, ymm10, ymm11
	add r9, r13
	mov r13, r10
	vpaddq ymm5, ymm5, ymm10
	xor r13, r11
	and r14, r13
	vmovdqu YMMWORD PTR [rcx+rdx*2+416], ymm5
	xor r14, r11
	add r9, r14
	vpalignr ymm8, ymm7, ymm6, 8
	add r8, QWORD PTR [rsi+rdx*1+96]
	add r8, QWORD PTR [rcx+rdx*2+192]
	mov r14, rax
	vpalignr ymm9, ymm3, ymm2, 8
	and r14, rbx
	andn r15, rax, rbp
	vpaddq ymm6, ymm6, ymm9
	add r14, r15
	add r8, r14
	vpsrlq ymm10, ymm8, 1
	rorx r14, rax, 14
	rorx r15, rax, 18
	vpsllq ymm11, ymm8, 63
	xor r14, r15
	rorx r15, rax, 41
	vpxor ymm10, ymm10, ymm11
	xor r14, r15
	add r8, r14
	vpsrlq ymm11, ymm8, 8
	add r12, r8
	rorx r14, r9, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r9, 34
	xor r14, r15
	vpsllq ymm11, ymm8, 56
	rorx r15, r9, 39
	xor r14, r15
	vpxor ymm10, ymm10, ymm11
	add r8, r14
	mov r14, r9
	vpsrlq ymm11, ymm8, 7
	xor r14, r10
	and r13, r14
	vpxor ymm10, ymm10, ymm11
	xor r13, r10
	add r8, r13
	vpaddq ymm6, ymm6, ymm10
	add rbp, QWORD PTR [rsi+rdx*1+104]
	add rbp, QWORD PTR [rcx+rdx*2+200]
	mov r13, r12
	vpsrlq ymm10, ymm5, 19
	and r13, rax
	andn r15, r12, rbx
	vpsllq ymm11, ymm5, 45
	add r13, r15
	add rbp, r13
	vpxor ymm10, ymm10, ymm11
	rorx r13, r12, 14
	rorx r15, r12, 18
	vpsrlq ymm11, ymm5, 61
	xor r13, r15
	rorx r15, r12, 41
	vpxor ymm10, ymm10, ymm11
	xor r13, r15
	add rbp, r13
	vpsllq ymm11, ymm5, 3
	add r11, rbp
	rorx r13, r8, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r8, 34
	xor r13, r15
	vpsrlq ymm11, ymm5, 6
	rorx r15, r8, 39
	xor r13, r15
	vpxor ymm10, ymm10, ymm11
	add rbp, r13
	mov r13, r8
	vpaddq ymm6, ymm6, ymm10
	xor r13, r9
	and r14, r13
	vmovdqu YMMWORD PTR [rcx+rdx*2+448], ymm6
	xor r14, r9
	add rbp, r14
	vpalignr ymm8, ymm0, ymm7, 8
	add rbx, QWORD PTR [rsi+rdx*1+112]
	add rbx, QWORD PTR [rcx+rdx*2+224]
	mov r14, r11
	vpalignr ymm9, ymm4, ymm3, 8
	and r14, r12
	andn r15, r11, rax
	vpaddq ymm7, ymm7, ymm9
	add r14, r15
	add rbx, r14
	vpsrlq ymm10, ymm8, 1
	rorx r14, r11, 14
	rorx r15, r11, 18
	vpsllq ymm11, ymm8, 63
	xor r14, r15
	rorx r15, r11, 41
	vpxor ymm10, ymm10, ymm11
	xor r14, r15
	add rbx, r14
	vpsrlq ymm11, ymm8, 8
	add r10, rbx
	rorx r14, rbp, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, rbp, 34
	xor r14, r15
	vpsllq ymm11, ymm8, 56
	rorx r15, rbp, 39
	xor r14, r15
	vpxor ymm10, ymm10, ymm11
	add rbx, r14
	mov r14, rbp
	vpsrlq ymm11, ymm8, 7
	xor r14, r8
	and r13, r14
	vpxor ymm10, ymm10, ymm11
	xor r13, r8
	add rbx, r13
	vpaddq ymm7, ymm7, ymm10
	add rax, QWORD PTR [rsi+rdx*1+120]
	add rax, QWORD PTR [rcx+rdx*2+232]
	mov r13, r10
	vpsrlq ymm10, ymm6, 19
	and r13, r11
	andn r15, r10, r12
	vpsllq ymm11, ymm6, 45
	add r13, r15
	add rax, r13
	vpxor ymm10, ymm10, ymm11
	rorx r13, r10, 14
	rorx r15, r10, 18
	vpsrlq ymm11, ymm6, 61
	xor r13, r15
	rorx r15, r10, 41
	vpxor ymm10, ymm10, ymm11
	xor r13, r15
	add rax, r13
	vpsllq ymm11, ymm6, 3
	add r9, rax
	rorx r13, rbx, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, rbx, 34
	xor r13, r15
	vpsrlq ymm11, ymm6, 6
	rorx r15, rbx, 39
	xor r13, r15
	vpxor ymm10, ymm10, ymm11
	add rax, r13
	mov r13, rbx
	vpaddq ymm7, ymm7, ymm10
	xor r13, rbp
	and r14, r13
	vmovdqu YMMWORD PTR [rcx+rdx*2+480], ymm7
	xor r14, rbp
	add rax, r14
	add rdx, 128
	cmp rdx, 512
	jne 25b
	add r12, QWORD PTR [rsi+rdx*1]
	add r12, QWORD PTR [rcx+rdx*2]
	mov r14, r9
	and r14, r10
	andn r15, r9, r11
	add r14, r15
	add r12, r14
	rorx r14, r9, 14
	rorx r15, r9, 18
	xor r14, r15
	rorx r15, r9, 41
	xor r14, r15
	add r12, r14
	add r8, r12
	rorx r14, rax, 28
	rorx r15, rax, 34
	xor r14, r15
	rorx r15, rax, 39
	xor r14, r15
	add r12, r14
	mov r14, rax
	xor r14, rbx
	and r13, r14
	xor r13, rbx
	add r12, r13
	add r11, QWORD PTR [rsi+rdx*1+8]
	add r11, QWORD PTR [rcx+rdx*2+8]
	mov r13, r8
	and r13, r9
	andn r15, r8, r10
	add r13, r15
	add r11, r13
	rorx r13, r8, 14
	rorx r15, r8, 18
	xor r13, r15
	rorx r15, r8, 41
	xor r13, r15
	add r11, r13
	add rbp, r11
	rorx r13, r12, 28
	rorx r15, r12, 34
	xor r13, r15
	rorx r15, r12, 39
	xor r13, r15
	add r11, r13
	mov r13, r12
	xor r13, rax
	and r14, r13
	xor r14, rax
	add r11, r14
	add r10, QWORD PTR [rsi+rdx*1+16]
	add r10, QWORD PTR [rcx+rdx*2+32]
	mov r14, rbp
	and r14, r8
	andn r15, rbp, r9
	add r14, r15
	add r10, r14
	rorx r14, rbp, 14
	rorx r15, rbp, 18
	xor r14, r15
	rorx r15, rbp, 41
	xor r14, r15
	add r10, r14
	add rbx, r10
	rorx r14, r11, 28
	rorx r15, r11, 34
	xor r14, r15
	rorx r15, r11, 39
	xor r14, r15
	add r10, r14
	mov r14, r11
	xor r14, r12
	and r13, r14
	xor r13, r12
	add r10, r13
	add r9, QWORD PTR [rsi+rdx*1+24]
	add r9, QWORD PTR [rcx+rdx*2+40]
	mov r13, rbx
	and r13, rbp
	andn r15, rbx, r8
	add r13, r15
	add r9, r13
	rorx r13, rbx, 14
	rorx r15, rbx, 18
	xor r13, r15
	rorx r15, rbx, 41
	xor r13, r15
	add r9, r13
	add rax, r9
	rorx r13, r10, 28
	rorx r15, r10, 34
	xor r13, r15
	rorx r15, r10, 39
	xor r13, r15
	add r9, r13
	mov r13, r10
	xor r13, r11
	and r14, r13
	xor r14, r11
	add r9, r14
	add r8, QWORD PTR [rsi+rdx*1+32]
	add r8, QWORD PTR [rcx+rdx*2+64]
	mov r14, rax
	and r14, rbx
	andn r15, rax, rbp
	add r14, r15
	add r8, r14
	rorx r14, rax, 14
	rorx r15, rax, 18
	xor r14, r15
	rorx r15, rax, 41
	xor r14, r15
	add r8, r14
	add r12, r8
	rorx r14, r9, 28
	rorx r15, r9, 34
	xor r14, r15
	rorx r15, r9, 39
	xor r14, r15
	add r8, r14
	mov r14, r9
	xor r14, r10
	and r13, r14
	xor r13, r10
	add r8, r13
	add rbp, QWORD PTR [rsi+rdx*1+40]
	add rbp, QWORD PTR [rcx+rdx*2+72]
	mov r13, r12
	and r13, rax
	andn r15, r12, rbx
	add r13, r15
	add rbp, r13
	rorx r13, r12, 14
	rorx r15, r12, 18
	xor r13, r15
	rorx r15, r12, 41
	xor r13, r15
	add rbp, r13
	add r11, rbp
	rorx r13, r8, 28
	rorx r15, r8, 34
	xor r13, r15
	rorx r15, r8, 39
	xor r13, r15
	add rbp, r13
	mov r13, r8
	xor r13, r9
	and r14, r13
	xor r14, r9
	add rbp, r14
	add rbx, QWORD PTR [rsi+rdx*1+48]
	add rbx, QWORD PTR [rcx+rdx*2+96]
	mov r14, r11
	and r14, r12
	andn r15, r11, rax
	add r14, r15
	add rbx, r14
	rorx r14, r11, 14
	rorx r15, r11, 18
	xor r14, r15
	rorx r15, r11, 41
	xor r14, r15
	add rbx, r14
	add r10, rbx
	rorx r14, rbp, 28
	rorx r15, rbp, 34
	xor r14, r15
	rorx r15, rbp, 39
	xor r14, r15
	add rbx, r14
	mov r14, rbp
	xor r14, r8
	and r13, r14
	xor r13, r8
	add rbx, r13
	add rax, QWORD PTR [rsi+rdx*1+56]
	add rax, QWORD PTR [rcx+rdx*2+104]
	mov r13, r10
	and r13, r11
	andn r15, r10, r12
	add r13, r15
	add rax, r13
	rorx r13, r10, 14
	rorx r15, r10, 18
	xor r13, r15
	rorx r15, r10, 41
	xor r13, r15
	add rax, r13
	add r9, rax
	rorx r13, rbx, 28
	rorx r15, rbx, 34
	xor r13, r15
	rorx r15, rbx, 39
	xor r13, r15
	add rax, r13
	mov r13, rbx
	xor r13, rbp
	and r14, r13
	xor r14, rbp
	add rax, r14
	add r12, QWORD PTR [rsi+rdx*1+64]
	add r12, QWORD PTR [rcx+rdx*2+128]
	mov r14, r9
	and r14, r10
	andn r15, r9, r11
	add r14, r15
	add r12, r14
	rorx r14, r9, 14
	rorx r15, r9, 18
	xor r14, r15
	rorx r15, r9, 41
	xor r14, r15
	add r12, r14
	add r8, r12
	rorx r14, rax, 28
	rorx r15, rax, 34
	xor r14, r15
	rorx r15, rax, 39
	xor r14, r15
	add r12, r14
	mov r14, rax
	xor r14, rbx
	and r13, r14
	xor r13, rbx
	add r12, r13
	add r11, QWORD PTR [rsi+rdx*1+72]
	add r11, QWORD PTR [rcx+rdx*2+136]
	mov r13, r8
	and r13, r9
	andn r15, r8, r10
	add r13, r15
	add r11, r13
	rorx r13, r8, 14
	rorx r15, r8, 18
	xor r13, r15
	rorx r15, r8, 41
	xor r13, r15
	add r11, r13
	add rbp, r11
	rorx r13, r12, 28
	rorx r15, r12, 34
	xor r13, r15
	rorx r15, r12, 39
	xor r13, r15
	add r11, r13
	mov r13, r12
	xor r13, rax
	and r14, r13
	xor r14, rax
	add r11, r14
	add r10, QWORD PTR [rsi+rdx*1+80]
	add r10, QWORD PTR [rcx+rdx*2+160]
	mov r14, rbp
	and r14, r8
	andn r15, rbp, r9
	add r14, r15
	add r10, r14
	rorx r14, rbp, 14
	rorx r15, rbp, 18
	xor r14, r15
	rorx r15, rbp, 41
	xor r14, r15
	add r10, r14
	add rbx, r10
	rorx r14, r11, 28
	rorx r15, r11, 34
	xor r14, r15
	rorx r15, r11, 39
	xor r14, r15
	add r10, r14
	mov r14, r11
	xor r14, r12
	and r13, r14
	xor r13, r12
	add r10, r13
	add r9, QWORD PTR [rsi+rdx*1+88]
	add r9, QWORD PTR [rcx+rdx*2+168]
	mov r13, rbx
	and r13, rbp
	andn r15, rbx, r8
	add r13, r15
	add r9, r13
	rorx r13, rbx, 14
	rorx r15, rbx, 18
	xor r13, r15
	rorx r15, rbx, 41
	xor r13, r15
	add r9, r13
	add rax, r9
	rorx r13, r10, 28
	rorx r15, r10, 34
	xor r13, r15
	rorx r15, r10, 39
	xor r13, r15
	add r9, r13
	mov r13, r10
	xor r13, r11
	and r14, r13
	xor r14, r11
	add r9, r14
	add r8, QWORD PTR [rsi+rdx*1+96]
	add r8, QWORD PTR [rcx+rdx*2+192]
	mov r14, rax
	and r14, rbx
	andn r15, rax, rbp
	add r14, r15
	add r8, r14
	rorx r14, rax, 14
	rorx r15, rax, 18
	xor r14, r15
	rorx r15, rax, 41
	xor r14, r15
	add r8, r14
	add r12, r8
	rorx r14, r9, 28
	rorx r15, r9, 34
	xor r14, r15
	rorx r15, r9, 39
	xor r14, r15
	add r8, r14
	mov r14, r9
	xor r14, r10
	and r13, r14
	xor r13, r10
	add r8, r13
	add rbp, QWORD PTR [rsi+rdx*1+104]
	add rbp, QWORD PTR [rcx+rdx*2+200]
	mov r13, r12
	and r13, rax
	andn r15, r12, rbx
	add r13, r15
	add rbp, r13
	rorx r13, r12, 14
	rorx r15, r12, 18
	xor r13, r15
	rorx r15, r12, 41
	xor r13, r15
	add rbp, r13
	add r11, rbp
	rorx r13, r8, 28
	rorx r15, r8, 34
	xor r13, r15
	rorx r15, r8, 39
	xor r13, r15
	add rbp, r13
	mov r13, r8
	xor r13, r9
	and r14, r13
	xor r14, r9
	add rbp, r14
	add rbx, QWORD PTR [rsi+rdx*1+112]
	add rbx, QWORD PTR [rcx+rdx*2+224]
	mov r14, r11
	and r14, r12
	andn r15, r11, rax
	add r14, r15
	add rbx, r14
	rorx r14, r11, 14
	rorx r15, r11, 18
	xor r14, r15
	rorx r15, r11, 41
	xor r14, r15
	add rbx, r14
	add r10, rbx
	rorx r14, rbp, 28
	rorx r15, rbp, 34
	xor r14, r15
	rorx r15, rbp, 39
	xor r14, r15
	add rbx, r14
	mov r14, rbp
	xor r14, r8
	and r13, r14
	xor r13, r8
	add rbx, r13
	add rax, QWORD PTR [rsi+rdx*1+120]
	add rax, QWORD PTR [rcx+rdx*2+232]
	mov r13, r10
	and r13, r11
	andn r15, r10, r12
	add r13, r15
	add rax, r13
	rorx r13, r10, 14
	rorx r15, r10, 18
	xor r13, r15
	rorx r15, r10, 41
	xor r13, r15
	add rax, r13
	add r9, rax
	rorx r13, rbx, 28
	rorx r15, rbx, 34
	xor r13, r15
	rorx r15, rbx, 39
	xor r13, r15
	add rax, r13
	mov r13, rbx
	xor r13, rbp
	and r14, r13
	xor r14, rbp
	add rax, r14
	mov rsi, QWORD PTR [rcx+1312]
	mov rdx, QWORD PTR [rcx+1320]
	add rax, QWORD PTR [rdi]
	add rbx, QWORD PTR [rdi+8]
	add rbp, QWORD PTR [rdi+16]
	add r8, QWORD PTR [rdi+24]
	add r9, QWORD PTR [rdi+32]
	add r10, QWORD PTR [rdi+40]
	add r11, QWORD PTR [rdi+48]
	add r12, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], rbp
	mov QWORD PTR [rdi+24], r8
	mov QWORD PTR [rdi+32], r9
	mov QWORD PTR [rdi+40], r10
	mov QWORD PTR [rdi+48], r11
	mov QWORD PTR [rdi+56], r12
	cmp rdx, 1
	je 26f
	mov r13, rbx
	xor r13, rbp
	mov QWORD PTR [rcx+1312], rsi
	mov QWORD PTR [rcx+1320], rdx
	lea rsi, {VG_SHA512_K}
	mov rdx, 0
28:
	add r12, QWORD PTR [rsi+rdx*1]
	add r12, QWORD PTR [rcx+rdx*2+16]
	mov r14, r9
	and r14, r10
	andn r15, r9, r11
	add r14, r15
	add r12, r14
	rorx r14, r9, 14
	rorx r15, r9, 18
	xor r14, r15
	rorx r15, r9, 41
	xor r14, r15
	add r12, r14
	add r8, r12
	rorx r14, rax, 28
	rorx r15, rax, 34
	xor r14, r15
	rorx r15, rax, 39
	xor r14, r15
	add r12, r14
	mov r14, rax
	xor r14, rbx
	and r13, r14
	xor r13, rbx
	add r12, r13
	add r11, QWORD PTR [rsi+rdx*1+8]
	add r11, QWORD PTR [rcx+rdx*2+24]
	mov r13, r8
	and r13, r9
	andn r15, r8, r10
	add r13, r15
	add r11, r13
	rorx r13, r8, 14
	rorx r15, r8, 18
	xor r13, r15
	rorx r15, r8, 41
	xor r13, r15
	add r11, r13
	add rbp, r11
	rorx r13, r12, 28
	rorx r15, r12, 34
	xor r13, r15
	rorx r15, r12, 39
	xor r13, r15
	add r11, r13
	mov r13, r12
	xor r13, rax
	and r14, r13
	xor r14, rax
	add r11, r14
	add r10, QWORD PTR [rsi+rdx*1+16]
	add r10, QWORD PTR [rcx+rdx*2+48]
	mov r14, rbp
	and r14, r8
	andn r15, rbp, r9
	add r14, r15
	add r10, r14
	rorx r14, rbp, 14
	rorx r15, rbp, 18
	xor r14, r15
	rorx r15, rbp, 41
	xor r14, r15
	add r10, r14
	add rbx, r10
	rorx r14, r11, 28
	rorx r15, r11, 34
	xor r14, r15
	rorx r15, r11, 39
	xor r14, r15
	add r10, r14
	mov r14, r11
	xor r14, r12
	and r13, r14
	xor r13, r12
	add r10, r13
	add r9, QWORD PTR [rsi+rdx*1+24]
	add r9, QWORD PTR [rcx+rdx*2+56]
	mov r13, rbx
	and r13, rbp
	andn r15, rbx, r8
	add r13, r15
	add r9, r13
	rorx r13, rbx, 14
	rorx r15, rbx, 18
	xor r13, r15
	rorx r15, rbx, 41
	xor r13, r15
	add r9, r13
	add rax, r9
	rorx r13, r10, 28
	rorx r15, r10, 34
	xor r13, r15
	rorx r15, r10, 39
	xor r13, r15
	add r9, r13
	mov r13, r10
	xor r13, r11
	and r14, r13
	xor r14, r11
	add r9, r14
	add r8, QWORD PTR [rsi+rdx*1+32]
	add r8, QWORD PTR [rcx+rdx*2+80]
	mov r14, rax
	and r14, rbx
	andn r15, rax, rbp
	add r14, r15
	add r8, r14
	rorx r14, rax, 14
	rorx r15, rax, 18
	xor r14, r15
	rorx r15, rax, 41
	xor r14, r15
	add r8, r14
	add r12, r8
	rorx r14, r9, 28
	rorx r15, r9, 34
	xor r14, r15
	rorx r15, r9, 39
	xor r14, r15
	add r8, r14
	mov r14, r9
	xor r14, r10
	and r13, r14
	xor r13, r10
	add r8, r13
	add rbp, QWORD PTR [rsi+rdx*1+40]
	add rbp, QWORD PTR [rcx+rdx*2+88]
	mov r13, r12
	and r13, rax
	andn r15, r12, rbx
	add r13, r15
	add rbp, r13
	rorx r13, r12, 14
	rorx r15, r12, 18
	xor r13, r15
	rorx r15, r12, 41
	xor r13, r15
	add rbp, r13
	add r11, rbp
	rorx r13, r8, 28
	rorx r15, r8, 34
	xor r13, r15
	rorx r15, r8, 39
	xor r13, r15
	add rbp, r13
	mov r13, r8
	xor r13, r9
	and r14, r13
	xor r14, r9
	add rbp, r14
	add rbx, QWORD PTR [rsi+rdx*1+48]
	add rbx, QWORD PTR [rcx+rdx*2+112]
	mov r14, r11
	and r14, r12
	andn r15, r11, rax
	add r14, r15
	add rbx, r14
	rorx r14, r11, 14
	rorx r15, r11, 18
	xor r14, r15
	rorx r15, r11, 41
	xor r14, r15
	add rbx, r14
	add r10, rbx
	rorx r14, rbp, 28
	rorx r15, rbp, 34
	xor r14, r15
	rorx r15, rbp, 39
	xor r14, r15
	add rbx, r14
	mov r14, rbp
	xor r14, r8
	and r13, r14
	xor r13, r8
	add rbx, r13
	add rax, QWORD PTR [rsi+rdx*1+56]
	add rax, QWORD PTR [rcx+rdx*2+120]
	mov r13, r10
	and r13, r11
	andn r15, r10, r12
	add r13, r15
	add rax, r13
	rorx r13, r10, 14
	rorx r15, r10, 18
	xor r13, r15
	rorx r15, r10, 41
	xor r13, r15
	add rax, r13
	add r9, rax
	rorx r13, rbx, 28
	rorx r15, rbx, 34
	xor r13, r15
	rorx r15, rbx, 39
	xor r13, r15
	add rax, r13
	mov r13, rbx
	xor r13, rbp
	and r14, r13
	xor r14, rbp
	add rax, r14
	add r12, QWORD PTR [rsi+rdx*1+64]
	add r12, QWORD PTR [rcx+rdx*2+144]
	mov r14, r9
	and r14, r10
	andn r15, r9, r11
	add r14, r15
	add r12, r14
	rorx r14, r9, 14
	rorx r15, r9, 18
	xor r14, r15
	rorx r15, r9, 41
	xor r14, r15
	add r12, r14
	add r8, r12
	rorx r14, rax, 28
	rorx r15, rax, 34
	xor r14, r15
	rorx r15, rax, 39
	xor r14, r15
	add r12, r14
	mov r14, rax
	xor r14, rbx
	and r13, r14
	xor r13, rbx
	add r12, r13
	add r11, QWORD PTR [rsi+rdx*1+72]
	add r11, QWORD PTR [rcx+rdx*2+152]
	mov r13, r8
	and r13, r9
	andn r15, r8, r10
	add r13, r15
	add r11, r13
	rorx r13, r8, 14
	rorx r15, r8, 18
	xor r13, r15
	rorx r15, r8, 41
	xor r13, r15
	add r11, r13
	add rbp, r11
	rorx r13, r12, 28
	rorx r15, r12, 34
	xor r13, r15
	rorx r15, r12, 39
	xor r13, r15
	add r11, r13
	mov r13, r12
	xor r13, rax
	and r14, r13
	xor r14, rax
	add r11, r14
	add r10, QWORD PTR [rsi+rdx*1+80]
	add r10, QWORD PTR [rcx+rdx*2+176]
	mov r14, rbp
	and r14, r8
	andn r15, rbp, r9
	add r14, r15
	add r10, r14
	rorx r14, rbp, 14
	rorx r15, rbp, 18
	xor r14, r15
	rorx r15, rbp, 41
	xor r14, r15
	add r10, r14
	add rbx, r10
	rorx r14, r11, 28
	rorx r15, r11, 34
	xor r14, r15
	rorx r15, r11, 39
	xor r14, r15
	add r10, r14
	mov r14, r11
	xor r14, r12
	and r13, r14
	xor r13, r12
	add r10, r13
	add r9, QWORD PTR [rsi+rdx*1+88]
	add r9, QWORD PTR [rcx+rdx*2+184]
	mov r13, rbx
	and r13, rbp
	andn r15, rbx, r8
	add r13, r15
	add r9, r13
	rorx r13, rbx, 14
	rorx r15, rbx, 18
	xor r13, r15
	rorx r15, rbx, 41
	xor r13, r15
	add r9, r13
	add rax, r9
	rorx r13, r10, 28
	rorx r15, r10, 34
	xor r13, r15
	rorx r15, r10, 39
	xor r13, r15
	add r9, r13
	mov r13, r10
	xor r13, r11
	and r14, r13
	xor r14, r11
	add r9, r14
	add r8, QWORD PTR [rsi+rdx*1+96]
	add r8, QWORD PTR [rcx+rdx*2+208]
	mov r14, rax
	and r14, rbx
	andn r15, rax, rbp
	add r14, r15
	add r8, r14
	rorx r14, rax, 14
	rorx r15, rax, 18
	xor r14, r15
	rorx r15, rax, 41
	xor r14, r15
	add r8, r14
	add r12, r8
	rorx r14, r9, 28
	rorx r15, r9, 34
	xor r14, r15
	rorx r15, r9, 39
	xor r14, r15
	add r8, r14
	mov r14, r9
	xor r14, r10
	and r13, r14
	xor r13, r10
	add r8, r13
	add rbp, QWORD PTR [rsi+rdx*1+104]
	add rbp, QWORD PTR [rcx+rdx*2+216]
	mov r13, r12
	and r13, rax
	andn r15, r12, rbx
	add r13, r15
	add rbp, r13
	rorx r13, r12, 14
	rorx r15, r12, 18
	xor r13, r15
	rorx r15, r12, 41
	xor r13, r15
	add rbp, r13
	add r11, rbp
	rorx r13, r8, 28
	rorx r15, r8, 34
	xor r13, r15
	rorx r15, r8, 39
	xor r13, r15
	add rbp, r13
	mov r13, r8
	xor r13, r9
	and r14, r13
	xor r14, r9
	add rbp, r14
	add rbx, QWORD PTR [rsi+rdx*1+112]
	add rbx, QWORD PTR [rcx+rdx*2+240]
	mov r14, r11
	and r14, r12
	andn r15, r11, rax
	add r14, r15
	add rbx, r14
	rorx r14, r11, 14
	rorx r15, r11, 18
	xor r14, r15
	rorx r15, r11, 41
	xor r14, r15
	add rbx, r14
	add r10, rbx
	rorx r14, rbp, 28
	rorx r15, rbp, 34
	xor r14, r15
	rorx r15, rbp, 39
	xor r14, r15
	add rbx, r14
	mov r14, rbp
	xor r14, r8
	and r13, r14
	xor r13, r8
	add rbx, r13
	add rax, QWORD PTR [rsi+rdx*1+120]
	add rax, QWORD PTR [rcx+rdx*2+248]
	mov r13, r10
	and r13, r11
	andn r15, r10, r12
	add r13, r15
	add rax, r13
	rorx r13, r10, 14
	rorx r15, r10, 18
	xor r13, r15
	rorx r15, r10, 41
	xor r13, r15
	add rax, r13
	add r9, rax
	rorx r13, rbx, 28
	rorx r15, rbx, 34
	xor r13, r15
	rorx r15, rbx, 39
	xor r13, r15
	add rax, r13
	mov r13, rbx
	xor r13, rbp
	and r14, r13
	xor r14, rbp
	add rax, r14
	add rdx, 128
	cmp rdx, 640
	jne 28b
	mov rsi, QWORD PTR [rcx+1312]
	mov rdx, QWORD PTR [rcx+1320]
	add rax, QWORD PTR [rdi]
	add rbx, QWORD PTR [rdi+8]
	add rbp, QWORD PTR [rdi+16]
	add r8, QWORD PTR [rdi+24]
	add r9, QWORD PTR [rdi+32]
	add r10, QWORD PTR [rdi+40]
	add r11, QWORD PTR [rdi+48]
	add r12, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], rbp
	mov QWORD PTR [rdi+24], r8
	mov QWORD PTR [rdi+32], r9
	mov QWORD PTR [rdi+40], r10
	mov QWORD PTR [rdi+48], r11
	mov QWORD PTR [rdi+56], r12
	add rsi, 256
	sub rdx, 2
	jmp 27f
26:
	add rsi, 128
	sub rdx, 1
27:
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [rcx+1280]
	mov rbp, QWORD PTR [rcx+1288]
	mov r12, QWORD PTR [rcx+1296]
	mov r13, QWORD PTR [rcx+1304]
	vzeroupper
	movq r14, xmm14
	movq r15, xmm15
	ret
	.p2align 6

vg_sha512_compress_shani:
	movabs rax, 283686952306183
	vmovq xmm8, rax
	movabs rax, 579005069656919567
	vmovq xmm11, rax
	vpunpcklqdq xmm8, xmm8, xmm11
	vinserti128 ymm8, ymm8, xmm8, 1
	lea rax, {VG_SHA512_K}
	vmovdqu ymm1, YMMWORD PTR [rdi]
	vmovdqu ymm2, YMMWORD PTR [rdi+32]
	vperm2i128 ymm7, ymm2, ymm1, 32
	vperm2i128 ymm2, ymm2, ymm1, 49
	vpermq ymm1, ymm7, 177
	vpermq ymm2, ymm2, 177
	test rdx, rdx
	je 20f
22:
	vmovdqa ymm9, ymm1
	vmovdqa ymm10, ymm2
	vmovdqu ymm3, YMMWORD PTR [rsi]
	vpshufb ymm3, ymm3, ymm8
	vmovdqu ymm0, YMMWORD PTR [rax]
	vpaddq ymm0, ymm0, ymm3
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vmovdqu ymm4, YMMWORD PTR [rsi+32]
	vpshufb ymm4, ymm4, ymm8
	vmovdqu ymm0, YMMWORD PTR [rax+32]
	vpaddq ymm0, ymm0, ymm4
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vmovdqu ymm5, YMMWORD PTR [rsi+64]
	vpshufb ymm5, ymm5, ymm8
	vmovdqu ymm0, YMMWORD PTR [rax+64]
	vpaddq ymm0, ymm0, ymm5
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vmovdqu ymm6, YMMWORD PTR [rsi+96]
	vpshufb ymm6, ymm6, ymm8
	vmovdqu ymm0, YMMWORD PTR [rax+96]
	vpaddq ymm0, ymm0, ymm6
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm3, xmm4
	vperm2i128 ymm7, ymm5, ymm6, 33
	vpalignr ymm7, ymm7, ymm5, 8
	vpaddq ymm3, ymm3, ymm7
	vsha512msg2 ymm3, ymm6
	vmovdqu ymm0, YMMWORD PTR [rax+128]
	vpaddq ymm0, ymm0, ymm3
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm4, xmm5
	vperm2i128 ymm7, ymm6, ymm3, 33
	vpalignr ymm7, ymm7, ymm6, 8
	vpaddq ymm4, ymm4, ymm7
	vsha512msg2 ymm4, ymm3
	vmovdqu ymm0, YMMWORD PTR [rax+160]
	vpaddq ymm0, ymm0, ymm4
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm5, xmm6
	vperm2i128 ymm7, ymm3, ymm4, 33
	vpalignr ymm7, ymm7, ymm3, 8
	vpaddq ymm5, ymm5, ymm7
	vsha512msg2 ymm5, ymm4
	vmovdqu ymm0, YMMWORD PTR [rax+192]
	vpaddq ymm0, ymm0, ymm5
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm6, xmm3
	vperm2i128 ymm7, ymm4, ymm5, 33
	vpalignr ymm7, ymm7, ymm4, 8
	vpaddq ymm6, ymm6, ymm7
	vsha512msg2 ymm6, ymm5
	vmovdqu ymm0, YMMWORD PTR [rax+224]
	vpaddq ymm0, ymm0, ymm6
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm3, xmm4
	vperm2i128 ymm7, ymm5, ymm6, 33
	vpalignr ymm7, ymm7, ymm5, 8
	vpaddq ymm3, ymm3, ymm7
	vsha512msg2 ymm3, ymm6
	vmovdqu ymm0, YMMWORD PTR [rax+256]
	vpaddq ymm0, ymm0, ymm3
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm4, xmm5
	vperm2i128 ymm7, ymm6, ymm3, 33
	vpalignr ymm7, ymm7, ymm6, 8
	vpaddq ymm4, ymm4, ymm7
	vsha512msg2 ymm4, ymm3
	vmovdqu ymm0, YMMWORD PTR [rax+288]
	vpaddq ymm0, ymm0, ymm4
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm5, xmm6
	vperm2i128 ymm7, ymm3, ymm4, 33
	vpalignr ymm7, ymm7, ymm3, 8
	vpaddq ymm5, ymm5, ymm7
	vsha512msg2 ymm5, ymm4
	vmovdqu ymm0, YMMWORD PTR [rax+320]
	vpaddq ymm0, ymm0, ymm5
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm6, xmm3
	vperm2i128 ymm7, ymm4, ymm5, 33
	vpalignr ymm7, ymm7, ymm4, 8
	vpaddq ymm6, ymm6, ymm7
	vsha512msg2 ymm6, ymm5
	vmovdqu ymm0, YMMWORD PTR [rax+352]
	vpaddq ymm0, ymm0, ymm6
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm3, xmm4
	vperm2i128 ymm7, ymm5, ymm6, 33
	vpalignr ymm7, ymm7, ymm5, 8
	vpaddq ymm3, ymm3, ymm7
	vsha512msg2 ymm3, ymm6
	vmovdqu ymm0, YMMWORD PTR [rax+384]
	vpaddq ymm0, ymm0, ymm3
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm4, xmm5
	vperm2i128 ymm7, ymm6, ymm3, 33
	vpalignr ymm7, ymm7, ymm6, 8
	vpaddq ymm4, ymm4, ymm7
	vsha512msg2 ymm4, ymm3
	vmovdqu ymm0, YMMWORD PTR [rax+416]
	vpaddq ymm0, ymm0, ymm4
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm5, xmm6
	vperm2i128 ymm7, ymm3, ymm4, 33
	vpalignr ymm7, ymm7, ymm3, 8
	vpaddq ymm5, ymm5, ymm7
	vsha512msg2 ymm5, ymm4
	vmovdqu ymm0, YMMWORD PTR [rax+448]
	vpaddq ymm0, ymm0, ymm5
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm6, xmm3
	vperm2i128 ymm7, ymm4, ymm5, 33
	vpalignr ymm7, ymm7, ymm4, 8
	vpaddq ymm6, ymm6, ymm7
	vsha512msg2 ymm6, ymm5
	vmovdqu ymm0, YMMWORD PTR [rax+480]
	vpaddq ymm0, ymm0, ymm6
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm3, xmm4
	vperm2i128 ymm7, ymm5, ymm6, 33
	vpalignr ymm7, ymm7, ymm5, 8
	vpaddq ymm3, ymm3, ymm7
	vsha512msg2 ymm3, ymm6
	vmovdqu ymm0, YMMWORD PTR [rax+512]
	vpaddq ymm0, ymm0, ymm3
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm4, xmm5
	vperm2i128 ymm7, ymm6, ymm3, 33
	vpalignr ymm7, ymm7, ymm6, 8
	vpaddq ymm4, ymm4, ymm7
	vsha512msg2 ymm4, ymm3
	vmovdqu ymm0, YMMWORD PTR [rax+544]
	vpaddq ymm0, ymm0, ymm4
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm5, xmm6
	vperm2i128 ymm7, ymm3, ymm4, 33
	vpalignr ymm7, ymm7, ymm3, 8
	vpaddq ymm5, ymm5, ymm7
	vsha512msg2 ymm5, ymm4
	vmovdqu ymm0, YMMWORD PTR [rax+576]
	vpaddq ymm0, ymm0, ymm5
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm6, xmm3
	vperm2i128 ymm7, ymm4, ymm5, 33
	vpalignr ymm7, ymm7, ymm4, 8
	vpaddq ymm6, ymm6, ymm7
	vsha512msg2 ymm6, ymm5
	vmovdqu ymm0, YMMWORD PTR [rax+608]
	vpaddq ymm0, ymm0, ymm6
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vpaddq ymm1, ymm1, ymm9
	vpaddq ymm2, ymm2, ymm10
	add rsi, 128
	sub rdx, 1
	jne 22b
	jmp 21f
20:
21:
	vpermq ymm1, ymm1, 177
	vpermq ymm2, ymm2, 177
	vperm2i128 ymm7, ymm1, ymm2, 49
	vperm2i128 ymm1, ymm1, ymm2, 32
	vmovdqu YMMWORD PTR [rdi], ymm7
	vmovdqu YMMWORD PTR [rdi+32], ymm1
	vzeroupper
	ret
	.p2align 6

vg_sha384_init:
	movabs rax, -3766243637369397544
	mov QWORD PTR [rdi], rax
	movabs rax, 7105036623409894663
	mov QWORD PTR [rdi+8], rax
	movabs rax, -7973340178411365097
	mov QWORD PTR [rdi+16], rax
	movabs rax, 1526699215303891257
	mov QWORD PTR [rdi+24], rax
	movabs rax, 7436329637833083697
	mov QWORD PTR [rdi+32], rax
	movabs rax, -8163818279084223215
	mov QWORD PTR [rdi+40], rax
	movabs rax, -2662702644619276377
	mov QWORD PTR [rdi+48], rax
	movabs rax, 5167115440072839076
	mov QWORD PTR [rdi+56], rax
	ret
	.p2align 6

vg_sha512_init:
	movabs rax, 7640891576956012808
	mov QWORD PTR [rdi], rax
	movabs rax, -4942790177534073029
	mov QWORD PTR [rdi+8], rax
	movabs rax, 4354685564936845355
	mov QWORD PTR [rdi+16], rax
	movabs rax, -6534734903238641935
	mov QWORD PTR [rdi+24], rax
	movabs rax, 5840696475078001361
	mov QWORD PTR [rdi+32], rax
	movabs rax, -7276294671716946913
	mov QWORD PTR [rdi+40], rax
	movabs rax, 2270897969802886507
	mov QWORD PTR [rdi+48], rax
	movabs rax, 6620516959819538809
	mov QWORD PTR [rdi+56], rax
	ret
	.p2align 6

vg_sha512_224_init:
	movabs rax, -8341449602262348382
	mov QWORD PTR [rdi], rax
	movabs rax, 8350123849800275158
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2160240930085379202
	mov QWORD PTR [rdi+16], rax
	movabs rax, 7466358040605728719
	mov QWORD PTR [rdi+24], rax
	movabs rax, 1111592415079452072
	mov QWORD PTR [rdi+32], rax
	movabs rax, 8638871050018654530
	mov QWORD PTR [rdi+40], rax
	movabs rax, 4583966954114332360
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1230299281376055969
	mov QWORD PTR [rdi+56], rax
	ret
	.p2align 6

vg_sha512_256_init:
	movabs rax, 2463787394917988140
	mov QWORD PTR [rdi], rax
	movabs rax, -6965556091613846334
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2563595384472711505
	mov QWORD PTR [rdi+16], rax
	movabs rax, -7622211418569250115
	mov QWORD PTR [rdi+24], rax
	movabs rax, -7626776825740460061
	mov QWORD PTR [rdi+32], rax
	movabs rax, -4729309413028513390
	mov QWORD PTR [rdi+40], rax
	movabs rax, 3098927326965381290
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1060366662362279074
	mov QWORD PTR [rdi+56], rax
	ret
	.p2align 6

vg_sha384_finalize:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha384_digest:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, -3766243637369397544
	mov QWORD PTR [rdi], rax
	movabs rax, 7105036623409894663
	mov QWORD PTR [rdi+8], rax
	movabs rax, -7973340178411365097
	mov QWORD PTR [rdi+16], rax
	movabs rax, 1526699215303891257
	mov QWORD PTR [rdi+24], rax
	movabs rax, 7436329637833083697
	mov QWORD PTR [rdi+32], rax
	movabs rax, -8163818279084223215
	mov QWORD PTR [rdi+40], rax
	movabs rax, -2662702644619276377
	mov QWORD PTR [rdi+48], rax
	movabs rax, 5167115440072839076
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha384_finalize_avx2:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha384_digest_avx2:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, -3766243637369397544
	mov QWORD PTR [rdi], rax
	movabs rax, 7105036623409894663
	mov QWORD PTR [rdi+8], rax
	movabs rax, -7973340178411365097
	mov QWORD PTR [rdi+16], rax
	movabs rax, 1526699215303891257
	mov QWORD PTR [rdi+24], rax
	movabs rax, 7436329637833083697
	mov QWORD PTR [rdi+32], rax
	movabs rax, -8163818279084223215
	mov QWORD PTR [rdi+40], rax
	movabs rax, -2662702644619276377
	mov QWORD PTR [rdi+48], rax
	movabs rax, 5167115440072839076
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha384_finalize_shani:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha384_digest_shani:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, -3766243637369397544
	mov QWORD PTR [rdi], rax
	movabs rax, 7105036623409894663
	mov QWORD PTR [rdi+8], rax
	movabs rax, -7973340178411365097
	mov QWORD PTR [rdi+16], rax
	movabs rax, 1526699215303891257
	mov QWORD PTR [rdi+24], rax
	movabs rax, 7436329637833083697
	mov QWORD PTR [rdi+32], rax
	movabs rax, -8163818279084223215
	mov QWORD PTR [rdi+40], rax
	movabs rax, -2662702644619276377
	mov QWORD PTR [rdi+48], rax
	movabs rax, 5167115440072839076
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_update:
	lea rsp, [rsp-1384]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1328], rbx
	mov QWORD PTR [r8+1336], rbp
	mov QWORD PTR [r8+1344], r12
	mov QWORD PTR [r8+1352], r13
	mov QWORD PTR [r8+1360], r14
	mov QWORD PTR [r8+1368], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 127
20:
	test r13, r13
	je 21f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 128
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 128
	jae 213f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 128
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 127
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 7
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_finalize:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_update_scratch:
	mov QWORD PTR [r8+1328], rbx
	mov QWORD PTR [r8+1336], rbp
	mov QWORD PTR [r8+1344], r12
	mov QWORD PTR [r8+1352], r13
	mov QWORD PTR [r8+1360], r14
	mov QWORD PTR [r8+1368], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 127
20:
	test r13, r13
	je 21f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 128
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 128
	jae 213f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 128
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 127
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 7
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	ret
	.p2align 6

vg_sha512_finalize_scratch:
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	ret
	.p2align 6

vg_sha512_digest:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, 7640891576956012808
	mov QWORD PTR [rdi], rax
	movabs rax, -4942790177534073029
	mov QWORD PTR [rdi+8], rax
	movabs rax, 4354685564936845355
	mov QWORD PTR [rdi+16], rax
	movabs rax, -6534734903238641935
	mov QWORD PTR [rdi+24], rax
	movabs rax, 5840696475078001361
	mov QWORD PTR [rdi+32], rax
	movabs rax, -7276294671716946913
	mov QWORD PTR [rdi+40], rax
	movabs rax, 2270897969802886507
	mov QWORD PTR [rdi+48], rax
	movabs rax, 6620516959819538809
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_update_avx2:
	lea rsp, [rsp-1384]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1328], rbx
	mov QWORD PTR [r8+1336], rbp
	mov QWORD PTR [r8+1344], r12
	mov QWORD PTR [r8+1352], r13
	mov QWORD PTR [r8+1360], r14
	mov QWORD PTR [r8+1368], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 127
20:
	test r13, r13
	je 21f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 128
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 128
	jae 213f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 128
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 127
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 7
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_finalize_avx2:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_update_scratch_avx2:
	mov QWORD PTR [r8+1328], rbx
	mov QWORD PTR [r8+1336], rbp
	mov QWORD PTR [r8+1344], r12
	mov QWORD PTR [r8+1352], r13
	mov QWORD PTR [r8+1360], r14
	mov QWORD PTR [r8+1368], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 127
20:
	test r13, r13
	je 21f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 128
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 128
	jae 213f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 128
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 127
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 7
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	ret
	.p2align 6

vg_sha512_finalize_scratch_avx2:
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	ret
	.p2align 6

vg_sha512_digest_avx2:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, 7640891576956012808
	mov QWORD PTR [rdi], rax
	movabs rax, -4942790177534073029
	mov QWORD PTR [rdi+8], rax
	movabs rax, 4354685564936845355
	mov QWORD PTR [rdi+16], rax
	movabs rax, -6534734903238641935
	mov QWORD PTR [rdi+24], rax
	movabs rax, 5840696475078001361
	mov QWORD PTR [rdi+32], rax
	movabs rax, -7276294671716946913
	mov QWORD PTR [rdi+40], rax
	movabs rax, 2270897969802886507
	mov QWORD PTR [rdi+48], rax
	movabs rax, 6620516959819538809
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_update_shani:
	lea rsp, [rsp-1384]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1328], rbx
	mov QWORD PTR [r8+1336], rbp
	mov QWORD PTR [r8+1344], r12
	mov QWORD PTR [r8+1352], r13
	mov QWORD PTR [r8+1360], r14
	mov QWORD PTR [r8+1368], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 127
20:
	test r13, r13
	je 21f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 128
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 128
	jae 213f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 128
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 127
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 7
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_finalize_shani:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_update_scratch_shani:
	mov QWORD PTR [r8+1328], rbx
	mov QWORD PTR [r8+1336], rbp
	mov QWORD PTR [r8+1344], r12
	mov QWORD PTR [r8+1352], r13
	mov QWORD PTR [r8+1360], r14
	mov QWORD PTR [r8+1368], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 127
20:
	test r13, r13
	je 21f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 128
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 128
	jae 213f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 128
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 127
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 7
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	ret
	.p2align 6

vg_sha512_finalize_scratch_shani:
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	ret
	.p2align 6

vg_sha512_digest_shani:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, 7640891576956012808
	mov QWORD PTR [rdi], rax
	movabs rax, -4942790177534073029
	mov QWORD PTR [rdi+8], rax
	movabs rax, 4354685564936845355
	mov QWORD PTR [rdi+16], rax
	movabs rax, -6534734903238641935
	mov QWORD PTR [rdi+24], rax
	movabs rax, 5840696475078001361
	mov QWORD PTR [rdi+32], rax
	movabs rax, -7276294671716946913
	mov QWORD PTR [rdi+40], rax
	movabs rax, 2270897969802886507
	mov QWORD PTR [rdi+48], rax
	movabs rax, 6620516959819538809
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_224_finalize:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_224_digest:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, -8341449602262348382
	mov QWORD PTR [rdi], rax
	movabs rax, 8350123849800275158
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2160240930085379202
	mov QWORD PTR [rdi+16], rax
	movabs rax, 7466358040605728719
	mov QWORD PTR [rdi+24], rax
	movabs rax, 1111592415079452072
	mov QWORD PTR [rdi+32], rax
	movabs rax, 8638871050018654530
	mov QWORD PTR [rdi+40], rax
	movabs rax, 4583966954114332360
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1230299281376055969
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_224_finalize_avx2:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_224_digest_avx2:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, -8341449602262348382
	mov QWORD PTR [rdi], rax
	movabs rax, 8350123849800275158
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2160240930085379202
	mov QWORD PTR [rdi+16], rax
	movabs rax, 7466358040605728719
	mov QWORD PTR [rdi+24], rax
	movabs rax, 1111592415079452072
	mov QWORD PTR [rdi+32], rax
	movabs rax, 8638871050018654530
	mov QWORD PTR [rdi+40], rax
	movabs rax, 4583966954114332360
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1230299281376055969
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_224_finalize_shani:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_224_digest_shani:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, -8341449602262348382
	mov QWORD PTR [rdi], rax
	movabs rax, 8350123849800275158
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2160240930085379202
	mov QWORD PTR [rdi+16], rax
	movabs rax, 7466358040605728719
	mov QWORD PTR [rdi+24], rax
	movabs rax, 1111592415079452072
	mov QWORD PTR [rdi+32], rax
	movabs rax, 8638871050018654530
	mov QWORD PTR [rdi+40], rax
	movabs rax, 4583966954114332360
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1230299281376055969
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_256_finalize:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_256_digest:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, 2463787394917988140
	mov QWORD PTR [rdi], rax
	movabs rax, -6965556091613846334
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2563595384472711505
	mov QWORD PTR [rdi+16], rax
	movabs rax, -7622211418569250115
	mov QWORD PTR [rdi+24], rax
	movabs rax, -7626776825740460061
	mov QWORD PTR [rdi+32], rax
	movabs rax, -4729309413028513390
	mov QWORD PTR [rdi+40], rax
	movabs rax, 3098927326965381290
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1060366662362279074
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_256_finalize_avx2:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_256_digest_avx2:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, 2463787394917988140
	mov QWORD PTR [rdi], rax
	movabs rax, -6965556091613846334
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2563595384472711505
	mov QWORD PTR [rdi+16], rax
	movabs rax, -7622211418569250115
	mov QWORD PTR [rdi+24], rax
	movabs rax, -7626776825740460061
	mov QWORD PTR [rdi+32], rax
	movabs rax, -4729309413028513390
	mov QWORD PTR [rdi+40], rax
	movabs rax, 3098927326965381290
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1060366662362279074
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_256_finalize_shani:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_256_digest_shani:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, 2463787394917988140
	mov QWORD PTR [rdi], rax
	movabs rax, -6965556091613846334
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2563595384472711505
	mov QWORD PTR [rdi+16], rax
	movabs rax, -7622211418569250115
	mov QWORD PTR [rdi+24], rax
	movabs rax, -7626776825740460061
	mov QWORD PTR [rdi+32], rax
	movabs rax, -4729309413028513390
	mov QWORD PTR [rdi+40], rax
	movabs rax, 3098927326965381290
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1060366662362279074
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6
