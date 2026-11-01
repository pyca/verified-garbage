// The functions of `src/internal/vg_sha512_compress.rs` of `verified-garbage-asm-x86_64`, as text: generated from
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
