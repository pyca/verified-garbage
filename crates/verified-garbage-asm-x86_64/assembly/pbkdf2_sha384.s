// The functions of `src/pbkdf2_sha384.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha384:
	lea rsp, [rsp-3432]
	mov rax, QWORD PTR [rsp+3440]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+1872], rbx
	mov QWORD PTR [r8+1880], rbp
	mov QWORD PTR [r8+1888], r12
	mov QWORD PTR [r8+1896], r13
	mov QWORD PTR [r8+1904], r14
	mov QWORD PTR [r8+1912], r15
	mov r15, r8
	mov QWORD PTR [r15+1920], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+1928], rax
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	cmp rbp, 129
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 2512
	call {vg_sha384_init}
	mov rdi, r15
	add rdi, 2512
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha512_update_scratch}
	mov rdi, r15
	add rdi, 2512
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2800
	mov rcx, r15
	call {vg_sha512_finalize_scratch}
	mov rdx, r15
	add rdx, 2800
	mov ecx, 48
21:
	mov rdi, r15
	add rdi, 1936
	mov rsi, r15
	add rsi, 2128
	mov r8, r15
	call {vg_hmac_sha384_init_scratch}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+1936]
	mov BYTE PTR [r15+r14*1+2320], al
	add r14, 1
	cmp r14, 192
	jne 22b
	mov rdi, r15
	add rdi, 2320
	mov esi, 128
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha512_update_scratch}
	mov rbp, r13
	mov r13, QWORD PTR [r15+1920]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+2320]
	mov BYTE PTR [r15+r14*1+2512], al
	add r14, 1
	cmp r14, 192
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+2864], eax
	mov rdi, r15
	add rdi, 2512
	mov rsi, rbp
	add rsi, 128
	mov rdx, r15
	add rdx, 2864
	mov ecx, 4
	mov r8, r15
	call {vg_sha512_update_scratch}
	mov rdi, r15
	add rdi, 2512
	mov rsi, r15
	add rsi, 2128
	mov rdx, rbp
	add rdx, 132
	mov rcx, r15
	add rcx, 2704
	mov r8, r15
	call {vg_hmac_sha384_finalize_scratch}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+2704]
	mov BYTE PTR [r15+r14*1+2752], al
	add r14, 1
	cmp r14, 48
	jne 27b
	mov rdi, r15
	add rdi, 1936
	mov rsi, r15
	add rsi, 2704
	mov rdx, QWORD PTR [r15+1928]
	mov rcx, r15
	add rcx, 2752
	mov r8, r15
	call {vg_pbkdf2_hmac_sha384_iterate}
	mov ecx, 48
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+2752]
	mov BYTE PTR [r13+r14*1], al
	add r14, 1
	cmp r14, rcx
	jne 210b
	add r13, rcx
	add rbx, 1
	sub r12, rcx
	jne 25b
	jmp 24f
23:
24:
	mov rbx, QWORD PTR [r15+1872]
	mov rbp, QWORD PTR [r15+1880]
	mov r12, QWORD PTR [r15+1888]
	mov r13, QWORD PTR [r15+1896]
	mov r14, QWORD PTR [r15+1904]
	mov r15, QWORD PTR [r15+1912]
	lea rsp, [rsp+3432]
	ret
	.p2align 6

vg_pbkdf2_hmac_sha384_avx2:
	lea rsp, [rsp-3432]
	mov rax, QWORD PTR [rsp+3440]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+1872], rbx
	mov QWORD PTR [r8+1880], rbp
	mov QWORD PTR [r8+1888], r12
	mov QWORD PTR [r8+1896], r13
	mov QWORD PTR [r8+1904], r14
	mov QWORD PTR [r8+1912], r15
	mov r15, r8
	mov QWORD PTR [r15+1920], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+1928], rax
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	cmp rbp, 129
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 2512
	call {vg_sha384_init}
	mov rdi, r15
	add rdi, 2512
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha512_update_scratch_avx2}
	mov rdi, r15
	add rdi, 2512
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2800
	mov rcx, r15
	call {vg_sha512_finalize_scratch_avx2}
	mov rdx, r15
	add rdx, 2800
	mov ecx, 48
21:
	mov rdi, r15
	add rdi, 1936
	mov rsi, r15
	add rsi, 2128
	mov r8, r15
	call {vg_hmac_sha384_init_scratch_avx2}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+1936]
	mov BYTE PTR [r15+r14*1+2320], al
	add r14, 1
	cmp r14, 192
	jne 22b
	mov rdi, r15
	add rdi, 2320
	mov esi, 128
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha512_update_scratch_avx2}
	mov rbp, r13
	mov r13, QWORD PTR [r15+1920]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+2320]
	mov BYTE PTR [r15+r14*1+2512], al
	add r14, 1
	cmp r14, 192
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+2864], eax
	mov rdi, r15
	add rdi, 2512
	mov rsi, rbp
	add rsi, 128
	mov rdx, r15
	add rdx, 2864
	mov ecx, 4
	mov r8, r15
	call {vg_sha512_update_scratch_avx2}
	mov rdi, r15
	add rdi, 2512
	mov rsi, r15
	add rsi, 2128
	mov rdx, rbp
	add rdx, 132
	mov rcx, r15
	add rcx, 2704
	mov r8, r15
	call {vg_hmac_sha384_finalize_scratch_avx2}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+2704]
	mov BYTE PTR [r15+r14*1+2752], al
	add r14, 1
	cmp r14, 48
	jne 27b
	mov rdi, r15
	add rdi, 1936
	mov rsi, r15
	add rsi, 2704
	mov rdx, QWORD PTR [r15+1928]
	mov rcx, r15
	add rcx, 2752
	mov r8, r15
	call {vg_pbkdf2_hmac_sha384_iterate_avx2}
	mov ecx, 48
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+2752]
	mov BYTE PTR [r13+r14*1], al
	add r14, 1
	cmp r14, rcx
	jne 210b
	add r13, rcx
	add rbx, 1
	sub r12, rcx
	jne 25b
	jmp 24f
23:
24:
	mov rbx, QWORD PTR [r15+1872]
	mov rbp, QWORD PTR [r15+1880]
	mov r12, QWORD PTR [r15+1888]
	mov r13, QWORD PTR [r15+1896]
	mov r14, QWORD PTR [r15+1904]
	mov r15, QWORD PTR [r15+1912]
	lea rsp, [rsp+3432]
	ret
	.p2align 6

vg_pbkdf2_hmac_sha384_shani:
	lea rsp, [rsp-3432]
	mov rax, QWORD PTR [rsp+3440]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+1872], rbx
	mov QWORD PTR [r8+1880], rbp
	mov QWORD PTR [r8+1888], r12
	mov QWORD PTR [r8+1896], r13
	mov QWORD PTR [r8+1904], r14
	mov QWORD PTR [r8+1912], r15
	mov r15, r8
	mov QWORD PTR [r15+1920], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+1928], rax
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	cmp rbp, 129
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 2512
	call {vg_sha384_init}
	mov rdi, r15
	add rdi, 2512
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha512_update_scratch_shani}
	mov rdi, r15
	add rdi, 2512
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2800
	mov rcx, r15
	call {vg_sha512_finalize_scratch_shani}
	mov rdx, r15
	add rdx, 2800
	mov ecx, 48
21:
	mov rdi, r15
	add rdi, 1936
	mov rsi, r15
	add rsi, 2128
	mov r8, r15
	call {vg_hmac_sha384_init_scratch_shani}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+1936]
	mov BYTE PTR [r15+r14*1+2320], al
	add r14, 1
	cmp r14, 192
	jne 22b
	mov rdi, r15
	add rdi, 2320
	mov esi, 128
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha512_update_scratch_shani}
	mov rbp, r13
	mov r13, QWORD PTR [r15+1920]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+2320]
	mov BYTE PTR [r15+r14*1+2512], al
	add r14, 1
	cmp r14, 192
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+2864], eax
	mov rdi, r15
	add rdi, 2512
	mov rsi, rbp
	add rsi, 128
	mov rdx, r15
	add rdx, 2864
	mov ecx, 4
	mov r8, r15
	call {vg_sha512_update_scratch_shani}
	mov rdi, r15
	add rdi, 2512
	mov rsi, r15
	add rsi, 2128
	mov rdx, rbp
	add rdx, 132
	mov rcx, r15
	add rcx, 2704
	mov r8, r15
	call {vg_hmac_sha384_finalize_scratch_shani}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+2704]
	mov BYTE PTR [r15+r14*1+2752], al
	add r14, 1
	cmp r14, 48
	jne 27b
	mov rdi, r15
	add rdi, 1936
	mov rsi, r15
	add rsi, 2704
	mov rdx, QWORD PTR [r15+1928]
	mov rcx, r15
	add rcx, 2752
	mov r8, r15
	call {vg_pbkdf2_hmac_sha384_iterate_shani}
	mov ecx, 48
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+2752]
	mov BYTE PTR [r13+r14*1], al
	add r14, 1
	cmp r14, rcx
	jne 210b
	add r13, rcx
	add rbx, 1
	sub r12, rcx
	jne 25b
	jmp 24f
23:
24:
	mov rbx, QWORD PTR [r15+1872]
	mov rbp, QWORD PTR [r15+1880]
	mov r12, QWORD PTR [r15+1888]
	mov r13, QWORD PTR [r15+1896]
	mov r14, QWORD PTR [r15+1904]
	mov r15, QWORD PTR [r15+1912]
	lea rsp, [rsp+3432]
	ret
	.p2align 6
