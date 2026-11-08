// The functions of `src/rsa_pss.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_sign_crt_ifma:
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
	mov rax, QWORD PTR [rsp+496]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+504]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+512]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+520]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	mov r11, QWORD PTR [rsp+528]
	mov r11, QWORD PTR [r11+40]
	mov QWORD PTR [rsp+376], r11
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
	mov rax, QWORD PTR [rsp+528]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+536]
	mov QWORD PTR [rsp+24], rax
	mov r11, QWORD PTR [rsp+376]
	cmp r11, 0
	je 22f
	cmp r11, 1
	je 24f
	cmp r11, 2
	je 26f
	cmp r11, 3
	je 28f
	cmp r11, 4
	je 210f
	cmp r11, 5
	je 212f
	cmp r11, 6
	je 214f
	call {vg_rsa_pss_sha512_256_encode}
	jmp 215f
214:
	call {vg_rsa_pss_sha512_224_encode}
215:
	jmp 213f
212:
	call {vg_rsa_pss_sha512_encode}
213:
	jmp 211f
210:
	call {vg_rsa_pss_sha384_encode}
211:
	jmp 29f
28:
	call {vg_rsa_pss_sha256_encode}
29:
	jmp 27f
26:
	call {vg_rsa_pss_sha224_encode}
27:
	jmp 25f
24:
	call {vg_rsa_pss_sha1_encode}
25:
	jmp 23f
22:
	call {vg_rsa_pss_md5_encode}
23:
	test eax, eax
	je 216f
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
	jmp 217f
216:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
217:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sign_crt_adx:
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
	mov rax, QWORD PTR [rsp+496]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+504]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+512]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+520]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	mov r11, QWORD PTR [rsp+528]
	mov r11, QWORD PTR [r11+40]
	mov QWORD PTR [rsp+376], r11
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
	mov rax, QWORD PTR [rsp+528]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+536]
	mov QWORD PTR [rsp+24], rax
	mov r11, QWORD PTR [rsp+376]
	cmp r11, 0
	je 22f
	cmp r11, 1
	je 24f
	cmp r11, 2
	je 26f
	cmp r11, 3
	je 28f
	cmp r11, 4
	je 210f
	cmp r11, 5
	je 212f
	cmp r11, 6
	je 214f
	call {vg_rsa_pss_sha512_256_encode}
	jmp 215f
214:
	call {vg_rsa_pss_sha512_224_encode}
215:
	jmp 213f
212:
	call {vg_rsa_pss_sha512_encode}
213:
	jmp 211f
210:
	call {vg_rsa_pss_sha384_encode}
211:
	jmp 29f
28:
	call {vg_rsa_pss_sha256_encode}
29:
	jmp 27f
26:
	call {vg_rsa_pss_sha224_encode}
27:
	jmp 25f
24:
	call {vg_rsa_pss_sha1_encode}
25:
	jmp 23f
22:
	call {vg_rsa_pss_md5_encode}
23:
	test eax, eax
	je 216f
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
	jmp 217f
216:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
217:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sign:
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
	mov rax, QWORD PTR [rsp+496]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+504]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+512]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+520]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	mov r11, QWORD PTR [rsp+528]
	mov r11, QWORD PTR [r11+40]
	mov QWORD PTR [rsp+376], r11
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
	mov rax, QWORD PTR [rsp+528]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+536]
	mov QWORD PTR [rsp+24], rax
	mov r11, QWORD PTR [rsp+376]
	cmp r11, 0
	je 22f
	cmp r11, 1
	je 24f
	cmp r11, 2
	je 26f
	cmp r11, 3
	je 28f
	cmp r11, 4
	je 210f
	cmp r11, 5
	je 212f
	cmp r11, 6
	je 214f
	call {vg_rsa_pss_sha512_256_encode}
	jmp 215f
214:
	call {vg_rsa_pss_sha512_224_encode}
215:
	jmp 213f
212:
	call {vg_rsa_pss_sha512_encode}
213:
	jmp 211f
210:
	call {vg_rsa_pss_sha384_encode}
211:
	jmp 29f
28:
	call {vg_rsa_pss_sha256_encode}
29:
	jmp 27f
26:
	call {vg_rsa_pss_sha224_encode}
27:
	jmp 25f
24:
	call {vg_rsa_pss_sha1_encode}
25:
	jmp 23f
22:
	call {vg_rsa_pss_md5_encode}
23:
	test eax, eax
	je 216f
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
	jmp 217f
216:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
217:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_verify_precomputed_rsa_ifma:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+144], rdi
	mov QWORD PTR [rsp+136], rsi
	mov QWORD PTR [rsp+152], rdx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+296], r8
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+304], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	mov r11, QWORD PTR [rsp+464]
	mov r11, QWORD PTR [r11+40]
	mov QWORD PTR [rsp+376], r11
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
	mov rdx, QWORD PTR [rsp+448]
	mov rcx, QWORD PTR [rsp+456]
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
	mov r8, QWORD PTR [rsp+416]
	mov r9, QWORD PTR [rsp+424]
	mov rax, QWORD PTR [rsp+136]
	add rax, 7
	shr rax, 3
	mov r10, QWORD PTR [rsp+176]
	sub r10, rax
	mov QWORD PTR [rsp+8], r10
	shl rax, 3
	add rax, rcx
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+24], rax
	mov rcx, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [rsp+376]
	cmp r11, 0
	je 22f
	cmp r11, 1
	je 24f
	cmp r11, 2
	je 26f
	cmp r11, 3
	je 28f
	cmp r11, 4
	je 210f
	cmp r11, 5
	je 212f
	cmp r11, 6
	je 214f
	call {vg_rsa_pss_sha512_256_check_encoding}
	jmp 215f
214:
	call {vg_rsa_pss_sha512_224_check_encoding}
215:
	jmp 213f
212:
	call {vg_rsa_pss_sha512_check_encoding}
213:
	jmp 211f
210:
	call {vg_rsa_pss_sha384_check_encoding}
211:
	jmp 29f
28:
	call {vg_rsa_pss_sha256_check_encoding}
29:
	jmp 27f
26:
	call {vg_rsa_pss_sha224_check_encoding}
27:
	jmp 25f
24:
	call {vg_rsa_pss_sha1_check_encoding}
25:
	jmp 23f
22:
	call {vg_rsa_pss_md5_check_encoding}
23:
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

vg_rsa_pss_verify_precomputed_rsa_adx:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+144], rdi
	mov QWORD PTR [rsp+136], rsi
	mov QWORD PTR [rsp+152], rdx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+296], r8
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+304], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	mov r11, QWORD PTR [rsp+464]
	mov r11, QWORD PTR [r11+40]
	mov QWORD PTR [rsp+376], r11
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
	mov rdx, QWORD PTR [rsp+448]
	mov rcx, QWORD PTR [rsp+456]
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
	mov r8, QWORD PTR [rsp+416]
	mov r9, QWORD PTR [rsp+424]
	mov rax, QWORD PTR [rsp+136]
	add rax, 7
	shr rax, 3
	mov r10, QWORD PTR [rsp+176]
	sub r10, rax
	mov QWORD PTR [rsp+8], r10
	shl rax, 3
	add rax, rcx
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+24], rax
	mov rcx, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [rsp+376]
	cmp r11, 0
	je 22f
	cmp r11, 1
	je 24f
	cmp r11, 2
	je 26f
	cmp r11, 3
	je 28f
	cmp r11, 4
	je 210f
	cmp r11, 5
	je 212f
	cmp r11, 6
	je 214f
	call {vg_rsa_pss_sha512_256_check_encoding}
	jmp 215f
214:
	call {vg_rsa_pss_sha512_224_check_encoding}
215:
	jmp 213f
212:
	call {vg_rsa_pss_sha512_check_encoding}
213:
	jmp 211f
210:
	call {vg_rsa_pss_sha384_check_encoding}
211:
	jmp 29f
28:
	call {vg_rsa_pss_sha256_check_encoding}
29:
	jmp 27f
26:
	call {vg_rsa_pss_sha224_check_encoding}
27:
	jmp 25f
24:
	call {vg_rsa_pss_sha1_check_encoding}
25:
	jmp 23f
22:
	call {vg_rsa_pss_md5_check_encoding}
23:
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

vg_rsa_pss_verify_precomputed:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+144], rdi
	mov QWORD PTR [rsp+136], rsi
	mov QWORD PTR [rsp+152], rdx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+296], r8
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+304], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	mov r11, QWORD PTR [rsp+464]
	mov r11, QWORD PTR [r11+40]
	mov QWORD PTR [rsp+376], r11
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
	mov rdx, QWORD PTR [rsp+448]
	mov rcx, QWORD PTR [rsp+456]
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
	mov r8, QWORD PTR [rsp+416]
	mov r9, QWORD PTR [rsp+424]
	mov rax, QWORD PTR [rsp+136]
	add rax, 7
	shr rax, 3
	mov r10, QWORD PTR [rsp+176]
	sub r10, rax
	mov QWORD PTR [rsp+8], r10
	shl rax, 3
	add rax, rcx
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+24], rax
	mov rcx, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [rsp+376]
	cmp r11, 0
	je 22f
	cmp r11, 1
	je 24f
	cmp r11, 2
	je 26f
	cmp r11, 3
	je 28f
	cmp r11, 4
	je 210f
	cmp r11, 5
	je 212f
	cmp r11, 6
	je 214f
	call {vg_rsa_pss_sha512_256_check_encoding}
	jmp 215f
214:
	call {vg_rsa_pss_sha512_224_check_encoding}
215:
	jmp 213f
212:
	call {vg_rsa_pss_sha512_check_encoding}
213:
	jmp 211f
210:
	call {vg_rsa_pss_sha384_check_encoding}
211:
	jmp 29f
28:
	call {vg_rsa_pss_sha256_check_encoding}
29:
	jmp 27f
26:
	call {vg_rsa_pss_sha224_check_encoding}
27:
	jmp 25f
24:
	call {vg_rsa_pss_sha1_check_encoding}
25:
	jmp 23f
22:
	call {vg_rsa_pss_md5_check_encoding}
23:
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
