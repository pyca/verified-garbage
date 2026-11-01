// The functions of `src/internal/vg_hmac_sha512_224_init_scratch_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha512_224_init_scratch_avx2:
	mov QWORD PTR [r8+1376], rbx
	mov QWORD PTR [r8+1384], rbp
	mov QWORD PTR [r8+1392], r12
	mov QWORD PTR [r8+1400], r13
	mov QWORD PTR [r8+1408], r14
	mov QWORD PTR [r8+1416], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha512_224_init}
	mov rdi, r12
	call {vg_sha512_224_init}
	mov eax, 909522486
	mov DWORD PTR [rbx+64], eax
	mov DWORD PTR [rbx+68], eax
	mov DWORD PTR [rbx+72], eax
	mov DWORD PTR [rbx+76], eax
	mov DWORD PTR [rbx+80], eax
	mov DWORD PTR [rbx+84], eax
	mov DWORD PTR [rbx+88], eax
	mov DWORD PTR [rbx+92], eax
	mov DWORD PTR [rbx+96], eax
	mov DWORD PTR [rbx+100], eax
	mov DWORD PTR [rbx+104], eax
	mov DWORD PTR [rbx+108], eax
	mov DWORD PTR [rbx+112], eax
	mov DWORD PTR [rbx+116], eax
	mov DWORD PTR [rbx+120], eax
	mov DWORD PTR [rbx+124], eax
	mov DWORD PTR [rbx+128], eax
	mov DWORD PTR [rbx+132], eax
	mov DWORD PTR [rbx+136], eax
	mov DWORD PTR [rbx+140], eax
	mov DWORD PTR [rbx+144], eax
	mov DWORD PTR [rbx+148], eax
	mov DWORD PTR [rbx+152], eax
	mov DWORD PTR [rbx+156], eax
	mov DWORD PTR [rbx+160], eax
	mov DWORD PTR [rbx+164], eax
	mov DWORD PTR [rbx+168], eax
	mov DWORD PTR [rbx+172], eax
	mov DWORD PTR [rbx+176], eax
	mov DWORD PTR [rbx+180], eax
	mov DWORD PTR [rbx+184], eax
	mov DWORD PTR [rbx+188], eax
	mov r14d, 0
	test r13, r13
	je 20f
22:
	movzx eax, BYTE PTR [rbp+r14*1]
	xor eax, 54
	mov BYTE PTR [rbx+r14*1+64], al
	add r14, 1
	cmp r14, r13
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [rbx+64]
	xor eax, 1785358954
	mov DWORD PTR [r12+64], eax
	mov eax, DWORD PTR [rbx+68]
	xor eax, 1785358954
	mov DWORD PTR [r12+68], eax
	mov eax, DWORD PTR [rbx+72]
	xor eax, 1785358954
	mov DWORD PTR [r12+72], eax
	mov eax, DWORD PTR [rbx+76]
	xor eax, 1785358954
	mov DWORD PTR [r12+76], eax
	mov eax, DWORD PTR [rbx+80]
	xor eax, 1785358954
	mov DWORD PTR [r12+80], eax
	mov eax, DWORD PTR [rbx+84]
	xor eax, 1785358954
	mov DWORD PTR [r12+84], eax
	mov eax, DWORD PTR [rbx+88]
	xor eax, 1785358954
	mov DWORD PTR [r12+88], eax
	mov eax, DWORD PTR [rbx+92]
	xor eax, 1785358954
	mov DWORD PTR [r12+92], eax
	mov eax, DWORD PTR [rbx+96]
	xor eax, 1785358954
	mov DWORD PTR [r12+96], eax
	mov eax, DWORD PTR [rbx+100]
	xor eax, 1785358954
	mov DWORD PTR [r12+100], eax
	mov eax, DWORD PTR [rbx+104]
	xor eax, 1785358954
	mov DWORD PTR [r12+104], eax
	mov eax, DWORD PTR [rbx+108]
	xor eax, 1785358954
	mov DWORD PTR [r12+108], eax
	mov eax, DWORD PTR [rbx+112]
	xor eax, 1785358954
	mov DWORD PTR [r12+112], eax
	mov eax, DWORD PTR [rbx+116]
	xor eax, 1785358954
	mov DWORD PTR [r12+116], eax
	mov eax, DWORD PTR [rbx+120]
	xor eax, 1785358954
	mov DWORD PTR [r12+120], eax
	mov eax, DWORD PTR [rbx+124]
	xor eax, 1785358954
	mov DWORD PTR [r12+124], eax
	mov eax, DWORD PTR [rbx+128]
	xor eax, 1785358954
	mov DWORD PTR [r12+128], eax
	mov eax, DWORD PTR [rbx+132]
	xor eax, 1785358954
	mov DWORD PTR [r12+132], eax
	mov eax, DWORD PTR [rbx+136]
	xor eax, 1785358954
	mov DWORD PTR [r12+136], eax
	mov eax, DWORD PTR [rbx+140]
	xor eax, 1785358954
	mov DWORD PTR [r12+140], eax
	mov eax, DWORD PTR [rbx+144]
	xor eax, 1785358954
	mov DWORD PTR [r12+144], eax
	mov eax, DWORD PTR [rbx+148]
	xor eax, 1785358954
	mov DWORD PTR [r12+148], eax
	mov eax, DWORD PTR [rbx+152]
	xor eax, 1785358954
	mov DWORD PTR [r12+152], eax
	mov eax, DWORD PTR [rbx+156]
	xor eax, 1785358954
	mov DWORD PTR [r12+156], eax
	mov eax, DWORD PTR [rbx+160]
	xor eax, 1785358954
	mov DWORD PTR [r12+160], eax
	mov eax, DWORD PTR [rbx+164]
	xor eax, 1785358954
	mov DWORD PTR [r12+164], eax
	mov eax, DWORD PTR [rbx+168]
	xor eax, 1785358954
	mov DWORD PTR [r12+168], eax
	mov eax, DWORD PTR [rbx+172]
	xor eax, 1785358954
	mov DWORD PTR [r12+172], eax
	mov eax, DWORD PTR [rbx+176]
	xor eax, 1785358954
	mov DWORD PTR [r12+176], eax
	mov eax, DWORD PTR [rbx+180]
	xor eax, 1785358954
	mov DWORD PTR [r12+180], eax
	mov eax, DWORD PTR [rbx+184]
	xor eax, 1785358954
	mov DWORD PTR [r12+184], eax
	mov eax, DWORD PTR [rbx+188]
	xor eax, 1785358954
	mov DWORD PTR [r12+188], eax
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+1376]
	mov rbp, QWORD PTR [r15+1384]
	mov r12, QWORD PTR [r15+1392]
	mov r13, QWORD PTR [r15+1400]
	mov r14, QWORD PTR [r15+1408]
	mov r15, QWORD PTR [r15+1416]
	ret
	.p2align 6
