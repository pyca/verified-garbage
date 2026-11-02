// The functions of `src/rsa_pss_sha224_mgf1_sha224.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_sha224_mgf1_sha224_sign_crt_adx:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+128], rdi
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+152], r8
	mov QWORD PTR [rsp+160], r9
	mov rax, QWORD PTR [rsp+480]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+488]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+496]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+504]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+512]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2560
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+296]
	mov rcx, QWORD PTR [rsp+312]
	mov r8, QWORD PTR [rsp+320]
	mov r9, QWORD PTR [rsp+216]
	mov rax, QWORD PTR [rsp+168]
	add rax, 4096
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 512
	mov QWORD PTR [rsp+8], rax
	call {vg_rsa_pss_sha224_mgf1_sha224_encode}
	test eax, eax
	je 22f
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+456]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+144]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_private_checked_adx}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
24:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 24b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
25:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 25b
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_sign:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+128], rdi
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+152], r8
	mov QWORD PTR [rsp+160], r9
	mov rax, QWORD PTR [rsp+480]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+488]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+496]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+504]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+512]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2560
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+296]
	mov rcx, QWORD PTR [rsp+312]
	mov r8, QWORD PTR [rsp+320]
	mov r9, QWORD PTR [rsp+216]
	mov rax, QWORD PTR [rsp+168]
	add rax, 4096
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 512
	mov QWORD PTR [rsp+8], rax
	call {vg_rsa_pss_sha224_mgf1_sha224_encode}
	test eax, eax
	je 22f
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+456]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+144]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_private_checked}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
24:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 24b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
25:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 25b
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_sign_crt_ifma:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+128], rdi
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+152], r8
	mov QWORD PTR [rsp+160], r9
	mov rax, QWORD PTR [rsp+480]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+488]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+496]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+504]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+512]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2560
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+296]
	mov rcx, QWORD PTR [rsp+312]
	mov r8, QWORD PTR [rsp+320]
	mov r9, QWORD PTR [rsp+216]
	mov rax, QWORD PTR [rsp+168]
	add rax, 4096
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 512
	mov QWORD PTR [rsp+8], rax
	call {vg_rsa_pss_sha224_mgf1_sha224_encode}
	test eax, eax
	je 22f
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+456]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+144]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_private_checked_ifma}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
24:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 24b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
25:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 25b
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_avx2_crt_adx:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+128], rdi
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+152], r8
	mov QWORD PTR [rsp+160], r9
	mov rax, QWORD PTR [rsp+480]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+488]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+496]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+504]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+512]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2560
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+296]
	mov rcx, QWORD PTR [rsp+312]
	mov r8, QWORD PTR [rsp+320]
	mov r9, QWORD PTR [rsp+216]
	mov rax, QWORD PTR [rsp+168]
	add rax, 4096
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 512
	mov QWORD PTR [rsp+8], rax
	call {vg_rsa_pss_sha224_mgf1_sha224_encode_avx2}
	test eax, eax
	je 22f
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+456]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+144]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_private_checked_adx}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
24:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 24b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
25:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 25b
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_avx2:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+128], rdi
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+152], r8
	mov QWORD PTR [rsp+160], r9
	mov rax, QWORD PTR [rsp+480]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+488]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+496]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+504]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+512]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2560
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+296]
	mov rcx, QWORD PTR [rsp+312]
	mov r8, QWORD PTR [rsp+320]
	mov r9, QWORD PTR [rsp+216]
	mov rax, QWORD PTR [rsp+168]
	add rax, 4096
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 512
	mov QWORD PTR [rsp+8], rax
	call {vg_rsa_pss_sha224_mgf1_sha224_encode_avx2}
	test eax, eax
	je 22f
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+456]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+144]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_private_checked}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
24:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 24b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
25:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 25b
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_avx2_crt_ifma:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+128], rdi
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+152], r8
	mov QWORD PTR [rsp+160], r9
	mov rax, QWORD PTR [rsp+480]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+488]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+496]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+504]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+512]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2560
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+296]
	mov rcx, QWORD PTR [rsp+312]
	mov r8, QWORD PTR [rsp+320]
	mov r9, QWORD PTR [rsp+216]
	mov rax, QWORD PTR [rsp+168]
	add rax, 4096
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 512
	mov QWORD PTR [rsp+8], rax
	call {vg_rsa_pss_sha224_mgf1_sha224_encode_avx2}
	test eax, eax
	je 22f
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+456]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+144]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_private_checked_ifma}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
24:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 24b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
25:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 25b
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_shani_crt_adx:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+128], rdi
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+152], r8
	mov QWORD PTR [rsp+160], r9
	mov rax, QWORD PTR [rsp+480]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+488]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+496]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+504]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+512]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2560
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+296]
	mov rcx, QWORD PTR [rsp+312]
	mov r8, QWORD PTR [rsp+320]
	mov r9, QWORD PTR [rsp+216]
	mov rax, QWORD PTR [rsp+168]
	add rax, 4096
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 512
	mov QWORD PTR [rsp+8], rax
	call {vg_rsa_pss_sha224_mgf1_sha224_encode_shani}
	test eax, eax
	je 22f
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+456]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+144]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_private_checked_adx}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
24:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 24b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
25:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 25b
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_shani:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+128], rdi
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+152], r8
	mov QWORD PTR [rsp+160], r9
	mov rax, QWORD PTR [rsp+480]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+488]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+496]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+504]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+512]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2560
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+296]
	mov rcx, QWORD PTR [rsp+312]
	mov r8, QWORD PTR [rsp+320]
	mov r9, QWORD PTR [rsp+216]
	mov rax, QWORD PTR [rsp+168]
	add rax, 4096
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 512
	mov QWORD PTR [rsp+8], rax
	call {vg_rsa_pss_sha224_mgf1_sha224_encode_shani}
	test eax, eax
	je 22f
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+456]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+144]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_private_checked}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
24:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 24b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
25:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 25b
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_shani_crt_ifma:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+128], rdi
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+152], r8
	mov QWORD PTR [rsp+160], r9
	mov rax, QWORD PTR [rsp+480]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+488]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+496]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+504]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+512]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2560
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+296]
	mov rcx, QWORD PTR [rsp+312]
	mov r8, QWORD PTR [rsp+320]
	mov r9, QWORD PTR [rsp+216]
	mov rax, QWORD PTR [rsp+168]
	add rax, 4096
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 512
	mov QWORD PTR [rsp+8], rax
	call {vg_rsa_pss_sha224_mgf1_sha224_encode_shani}
	test eax, eax
	je 22f
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+456]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+144]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_private_checked_ifma}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
24:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 24b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
25:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 25b
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_rsa_adx:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+144], rdi
	mov QWORD PTR [rsp+136], rsi
	mov QWORD PTR [rsp+152], rdx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+296], r8
	mov QWORD PTR [rsp+304], r9
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+440]
	mov rcx, QWORD PTR [rsp+448]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_public_precomputed_checked_adx}
	mov rcx, QWORD PTR [rsp+168]
	movzx r9d, BYTE PTR [rcx]
	mov r10, QWORD PTR [rsp+208]
	mov r11d, 0
	sub r11, r10
	and r9, r11
	cmp r9, 1
	sbb r9, r9
	mov QWORD PTR [rsp+264], r9
	mov rdi, QWORD PTR [rsp+296]
	mov rsi, rcx
	add rsi, r10
	mov rdx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+408]
	mov r9, QWORD PTR [rsp+416]
	mov rax, QWORD PTR [rsp+136]
	add rax, 7
	shr rax, 3
	mov r10, QWORD PTR [rsp+176]
	sub r10, rax
	mov QWORD PTR [rsp+8], r10
	shl rax, 3
	add rax, rcx
	mov QWORD PTR [rsp], rax
	mov rcx, QWORD PTR [rsp+216]
	call {vg_rsa_pss_sha224_mgf1_sha224_check_encoding}
	and rax, QWORD PTR [rsp+264]
	jmp 21f
20:
	mov eax, 0
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+144], rdi
	mov QWORD PTR [rsp+136], rsi
	mov QWORD PTR [rsp+152], rdx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+296], r8
	mov QWORD PTR [rsp+304], r9
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+440]
	mov rcx, QWORD PTR [rsp+448]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_public_precomputed_checked}
	mov rcx, QWORD PTR [rsp+168]
	movzx r9d, BYTE PTR [rcx]
	mov r10, QWORD PTR [rsp+208]
	mov r11d, 0
	sub r11, r10
	and r9, r11
	cmp r9, 1
	sbb r9, r9
	mov QWORD PTR [rsp+264], r9
	mov rdi, QWORD PTR [rsp+296]
	mov rsi, rcx
	add rsi, r10
	mov rdx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+408]
	mov r9, QWORD PTR [rsp+416]
	mov rax, QWORD PTR [rsp+136]
	add rax, 7
	shr rax, 3
	mov r10, QWORD PTR [rsp+176]
	sub r10, rax
	mov QWORD PTR [rsp+8], r10
	shl rax, 3
	add rax, rcx
	mov QWORD PTR [rsp], rax
	mov rcx, QWORD PTR [rsp+216]
	call {vg_rsa_pss_sha224_mgf1_sha224_check_encoding}
	and rax, QWORD PTR [rsp+264]
	jmp 21f
20:
	mov eax, 0
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_rsa_ifma:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+144], rdi
	mov QWORD PTR [rsp+136], rsi
	mov QWORD PTR [rsp+152], rdx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+296], r8
	mov QWORD PTR [rsp+304], r9
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+440]
	mov rcx, QWORD PTR [rsp+448]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_public_precomputed_checked_ifma}
	mov rcx, QWORD PTR [rsp+168]
	movzx r9d, BYTE PTR [rcx]
	mov r10, QWORD PTR [rsp+208]
	mov r11d, 0
	sub r11, r10
	and r9, r11
	cmp r9, 1
	sbb r9, r9
	mov QWORD PTR [rsp+264], r9
	mov rdi, QWORD PTR [rsp+296]
	mov rsi, rcx
	add rsi, r10
	mov rdx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+408]
	mov r9, QWORD PTR [rsp+416]
	mov rax, QWORD PTR [rsp+136]
	add rax, 7
	shr rax, 3
	mov r10, QWORD PTR [rsp+176]
	sub r10, rax
	mov QWORD PTR [rsp+8], r10
	shl rax, 3
	add rax, rcx
	mov QWORD PTR [rsp], rax
	mov rcx, QWORD PTR [rsp+216]
	call {vg_rsa_pss_sha224_mgf1_sha224_check_encoding}
	and rax, QWORD PTR [rsp+264]
	jmp 21f
20:
	mov eax, 0
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_avx2_rsa_adx:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+144], rdi
	mov QWORD PTR [rsp+136], rsi
	mov QWORD PTR [rsp+152], rdx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+296], r8
	mov QWORD PTR [rsp+304], r9
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+440]
	mov rcx, QWORD PTR [rsp+448]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_public_precomputed_checked_adx}
	mov rcx, QWORD PTR [rsp+168]
	movzx r9d, BYTE PTR [rcx]
	mov r10, QWORD PTR [rsp+208]
	mov r11d, 0
	sub r11, r10
	and r9, r11
	cmp r9, 1
	sbb r9, r9
	mov QWORD PTR [rsp+264], r9
	mov rdi, QWORD PTR [rsp+296]
	mov rsi, rcx
	add rsi, r10
	mov rdx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+408]
	mov r9, QWORD PTR [rsp+416]
	mov rax, QWORD PTR [rsp+136]
	add rax, 7
	shr rax, 3
	mov r10, QWORD PTR [rsp+176]
	sub r10, rax
	mov QWORD PTR [rsp+8], r10
	shl rax, 3
	add rax, rcx
	mov QWORD PTR [rsp], rax
	mov rcx, QWORD PTR [rsp+216]
	call {vg_rsa_pss_sha224_mgf1_sha224_check_encoding_avx2}
	and rax, QWORD PTR [rsp+264]
	jmp 21f
20:
	mov eax, 0
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_avx2:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+144], rdi
	mov QWORD PTR [rsp+136], rsi
	mov QWORD PTR [rsp+152], rdx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+296], r8
	mov QWORD PTR [rsp+304], r9
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+440]
	mov rcx, QWORD PTR [rsp+448]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_public_precomputed_checked}
	mov rcx, QWORD PTR [rsp+168]
	movzx r9d, BYTE PTR [rcx]
	mov r10, QWORD PTR [rsp+208]
	mov r11d, 0
	sub r11, r10
	and r9, r11
	cmp r9, 1
	sbb r9, r9
	mov QWORD PTR [rsp+264], r9
	mov rdi, QWORD PTR [rsp+296]
	mov rsi, rcx
	add rsi, r10
	mov rdx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+408]
	mov r9, QWORD PTR [rsp+416]
	mov rax, QWORD PTR [rsp+136]
	add rax, 7
	shr rax, 3
	mov r10, QWORD PTR [rsp+176]
	sub r10, rax
	mov QWORD PTR [rsp+8], r10
	shl rax, 3
	add rax, rcx
	mov QWORD PTR [rsp], rax
	mov rcx, QWORD PTR [rsp+216]
	call {vg_rsa_pss_sha224_mgf1_sha224_check_encoding_avx2}
	and rax, QWORD PTR [rsp+264]
	jmp 21f
20:
	mov eax, 0
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_avx2_rsa_ifma:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+144], rdi
	mov QWORD PTR [rsp+136], rsi
	mov QWORD PTR [rsp+152], rdx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+296], r8
	mov QWORD PTR [rsp+304], r9
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+440]
	mov rcx, QWORD PTR [rsp+448]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_public_precomputed_checked_ifma}
	mov rcx, QWORD PTR [rsp+168]
	movzx r9d, BYTE PTR [rcx]
	mov r10, QWORD PTR [rsp+208]
	mov r11d, 0
	sub r11, r10
	and r9, r11
	cmp r9, 1
	sbb r9, r9
	mov QWORD PTR [rsp+264], r9
	mov rdi, QWORD PTR [rsp+296]
	mov rsi, rcx
	add rsi, r10
	mov rdx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+408]
	mov r9, QWORD PTR [rsp+416]
	mov rax, QWORD PTR [rsp+136]
	add rax, 7
	shr rax, 3
	mov r10, QWORD PTR [rsp+176]
	sub r10, rax
	mov QWORD PTR [rsp+8], r10
	shl rax, 3
	add rax, rcx
	mov QWORD PTR [rsp], rax
	mov rcx, QWORD PTR [rsp+216]
	call {vg_rsa_pss_sha224_mgf1_sha224_check_encoding_avx2}
	and rax, QWORD PTR [rsp+264]
	jmp 21f
20:
	mov eax, 0
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_shani_rsa_adx:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+144], rdi
	mov QWORD PTR [rsp+136], rsi
	mov QWORD PTR [rsp+152], rdx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+296], r8
	mov QWORD PTR [rsp+304], r9
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+440]
	mov rcx, QWORD PTR [rsp+448]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_public_precomputed_checked_adx}
	mov rcx, QWORD PTR [rsp+168]
	movzx r9d, BYTE PTR [rcx]
	mov r10, QWORD PTR [rsp+208]
	mov r11d, 0
	sub r11, r10
	and r9, r11
	cmp r9, 1
	sbb r9, r9
	mov QWORD PTR [rsp+264], r9
	mov rdi, QWORD PTR [rsp+296]
	mov rsi, rcx
	add rsi, r10
	mov rdx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+408]
	mov r9, QWORD PTR [rsp+416]
	mov rax, QWORD PTR [rsp+136]
	add rax, 7
	shr rax, 3
	mov r10, QWORD PTR [rsp+176]
	sub r10, rax
	mov QWORD PTR [rsp+8], r10
	shl rax, 3
	add rax, rcx
	mov QWORD PTR [rsp], rax
	mov rcx, QWORD PTR [rsp+216]
	call {vg_rsa_pss_sha224_mgf1_sha224_check_encoding_shani}
	and rax, QWORD PTR [rsp+264]
	jmp 21f
20:
	mov eax, 0
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_shani:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+144], rdi
	mov QWORD PTR [rsp+136], rsi
	mov QWORD PTR [rsp+152], rdx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+296], r8
	mov QWORD PTR [rsp+304], r9
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+440]
	mov rcx, QWORD PTR [rsp+448]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_public_precomputed_checked}
	mov rcx, QWORD PTR [rsp+168]
	movzx r9d, BYTE PTR [rcx]
	mov r10, QWORD PTR [rsp+208]
	mov r11d, 0
	sub r11, r10
	and r9, r11
	cmp r9, 1
	sbb r9, r9
	mov QWORD PTR [rsp+264], r9
	mov rdi, QWORD PTR [rsp+296]
	mov rsi, rcx
	add rsi, r10
	mov rdx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+408]
	mov r9, QWORD PTR [rsp+416]
	mov rax, QWORD PTR [rsp+136]
	add rax, 7
	shr rax, 3
	mov r10, QWORD PTR [rsp+176]
	sub r10, rax
	mov QWORD PTR [rsp+8], r10
	shl rax, 3
	add rax, rcx
	mov QWORD PTR [rsp], rax
	mov rcx, QWORD PTR [rsp+216]
	call {vg_rsa_pss_sha224_mgf1_sha224_check_encoding_shani}
	and rax, QWORD PTR [rsp+264]
	jmp 21f
20:
	mov eax, 0
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_shani_rsa_ifma:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+144], rdi
	mov QWORD PTR [rsp+136], rsi
	mov QWORD PTR [rsp+152], rdx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+296], r8
	mov QWORD PTR [rsp+304], r9
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+440]
	mov rcx, QWORD PTR [rsp+448]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_public_precomputed_checked_ifma}
	mov rcx, QWORD PTR [rsp+168]
	movzx r9d, BYTE PTR [rcx]
	mov r10, QWORD PTR [rsp+208]
	mov r11d, 0
	sub r11, r10
	and r9, r11
	cmp r9, 1
	sbb r9, r9
	mov QWORD PTR [rsp+264], r9
	mov rdi, QWORD PTR [rsp+296]
	mov rsi, rcx
	add rsi, r10
	mov rdx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+408]
	mov r9, QWORD PTR [rsp+416]
	mov rax, QWORD PTR [rsp+136]
	add rax, 7
	shr rax, 3
	mov r10, QWORD PTR [rsp+176]
	sub r10, rax
	mov QWORD PTR [rsp+8], r10
	shl rax, 3
	add rax, rcx
	mov QWORD PTR [rsp], rax
	mov rcx, QWORD PTR [rsp+216]
	call {vg_rsa_pss_sha224_mgf1_sha224_check_encoding_shani}
	and rax, QWORD PTR [rsp+264]
	jmp 21f
20:
	mov eax, 0
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6
