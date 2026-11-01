// The functions of `src/internal/vg_pbkdf2_hmac_sha512_iterate_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha512_iterate_avx2:
	mov QWORD PTR [r8+1328], rbx
	mov QWORD PTR [r8+1336], rbp
	mov QWORD PTR [r8+1344], r12
	mov QWORD PTR [r8+1352], r13
	mov QWORD PTR [r8+1360], r14
	mov QWORD PTR [r8+1368], r15
	mov r15, r8
	mov r12, rdi
	mov r13, rcx
	mov r14d, edx
	mov rbx, r8
	add rbx, 1376
	mov rbp, r8
	add rbp, 1440
	mov eax, DWORD PTR [rsi]
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rsi+16]
	mov DWORD PTR [rbp+16], eax
	mov eax, DWORD PTR [rsi+20]
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rsi+24]
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rsi+28]
	mov DWORD PTR [rbp+28], eax
	mov eax, DWORD PTR [rsi+32]
	mov DWORD PTR [rbp+32], eax
	mov eax, DWORD PTR [rsi+36]
	mov DWORD PTR [rbp+36], eax
	mov eax, DWORD PTR [rsi+40]
	mov DWORD PTR [rbp+40], eax
	mov eax, DWORD PTR [rsi+44]
	mov DWORD PTR [rbp+44], eax
	mov eax, DWORD PTR [rsi+48]
	mov DWORD PTR [rbp+48], eax
	mov eax, DWORD PTR [rsi+52]
	mov DWORD PTR [rbp+52], eax
	mov eax, DWORD PTR [rsi+56]
	mov DWORD PTR [rbp+56], eax
	mov eax, DWORD PTR [rsi+60]
	mov DWORD PTR [rbp+60], eax
	mov eax, 128
	mov DWORD PTR [rbp+64], eax
	mov eax, 0
	mov DWORD PTR [rbp+68], eax
	mov DWORD PTR [rbp+72], eax
	mov DWORD PTR [rbp+76], eax
	mov DWORD PTR [rbp+80], eax
	mov DWORD PTR [rbp+84], eax
	mov DWORD PTR [rbp+88], eax
	mov DWORD PTR [rbp+92], eax
	mov DWORD PTR [rbp+96], eax
	mov DWORD PTR [rbp+100], eax
	mov DWORD PTR [rbp+104], eax
	mov DWORD PTR [rbp+108], eax
	mov r12d, 192
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
	mov r12, rdi
	test r14, r14
	je 20f
22:
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
	mov eax, DWORD PTR [r12+32]
	mov DWORD PTR [rbx+32], eax
	mov eax, DWORD PTR [r12+36]
	mov DWORD PTR [rbx+36], eax
	mov eax, DWORD PTR [r12+40]
	mov DWORD PTR [rbx+40], eax
	mov eax, DWORD PTR [r12+44]
	mov DWORD PTR [rbx+44], eax
	mov eax, DWORD PTR [r12+48]
	mov DWORD PTR [rbx+48], eax
	mov eax, DWORD PTR [r12+52]
	mov DWORD PTR [rbx+52], eax
	mov eax, DWORD PTR [r12+56]
	mov DWORD PTR [rbx+56], eax
	mov eax, DWORD PTR [r12+60]
	mov DWORD PTR [rbx+60], eax
	mov rsi, rbp
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
	mov eax, DWORD PTR [r12+192]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+196]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+200]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+204]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+208]
	mov DWORD PTR [rbx+16], eax
	mov eax, DWORD PTR [r12+212]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+216]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+220]
	mov DWORD PTR [rbx+28], eax
	mov eax, DWORD PTR [r12+224]
	mov DWORD PTR [rbx+32], eax
	mov eax, DWORD PTR [r12+228]
	mov DWORD PTR [rbx+36], eax
	mov eax, DWORD PTR [r12+232]
	mov DWORD PTR [rbx+40], eax
	mov eax, DWORD PTR [r12+236]
	mov DWORD PTR [rbx+44], eax
	mov eax, DWORD PTR [r12+240]
	mov DWORD PTR [rbx+48], eax
	mov eax, DWORD PTR [r12+244]
	mov DWORD PTR [rbx+52], eax
	mov eax, DWORD PTR [r12+248]
	mov DWORD PTR [rbx+56], eax
	mov eax, DWORD PTR [r12+252]
	mov DWORD PTR [rbx+60], eax
	mov rsi, rbp
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
	mov eax, DWORD PTR [rbp]
	xor eax, DWORD PTR [r13]
	mov DWORD PTR [r13], eax
	mov eax, DWORD PTR [rbp+4]
	xor eax, DWORD PTR [r13+4]
	mov DWORD PTR [r13+4], eax
	mov eax, DWORD PTR [rbp+8]
	xor eax, DWORD PTR [r13+8]
	mov DWORD PTR [r13+8], eax
	mov eax, DWORD PTR [rbp+12]
	xor eax, DWORD PTR [r13+12]
	mov DWORD PTR [r13+12], eax
	mov eax, DWORD PTR [rbp+16]
	xor eax, DWORD PTR [r13+16]
	mov DWORD PTR [r13+16], eax
	mov eax, DWORD PTR [rbp+20]
	xor eax, DWORD PTR [r13+20]
	mov DWORD PTR [r13+20], eax
	mov eax, DWORD PTR [rbp+24]
	xor eax, DWORD PTR [r13+24]
	mov DWORD PTR [r13+24], eax
	mov eax, DWORD PTR [rbp+28]
	xor eax, DWORD PTR [r13+28]
	mov DWORD PTR [r13+28], eax
	mov eax, DWORD PTR [rbp+32]
	xor eax, DWORD PTR [r13+32]
	mov DWORD PTR [r13+32], eax
	mov eax, DWORD PTR [rbp+36]
	xor eax, DWORD PTR [r13+36]
	mov DWORD PTR [r13+36], eax
	mov eax, DWORD PTR [rbp+40]
	xor eax, DWORD PTR [r13+40]
	mov DWORD PTR [r13+40], eax
	mov eax, DWORD PTR [rbp+44]
	xor eax, DWORD PTR [r13+44]
	mov DWORD PTR [r13+44], eax
	mov eax, DWORD PTR [rbp+48]
	xor eax, DWORD PTR [r13+48]
	mov DWORD PTR [r13+48], eax
	mov eax, DWORD PTR [rbp+52]
	xor eax, DWORD PTR [r13+52]
	mov DWORD PTR [r13+52], eax
	mov eax, DWORD PTR [rbp+56]
	xor eax, DWORD PTR [r13+56]
	mov DWORD PTR [r13+56], eax
	mov eax, DWORD PTR [rbp+60]
	xor eax, DWORD PTR [r13+60]
	mov DWORD PTR [r13+60], eax
	sub r14, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	ret
	.p2align 6
