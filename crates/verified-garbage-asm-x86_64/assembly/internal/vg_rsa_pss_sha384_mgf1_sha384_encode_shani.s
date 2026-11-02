// The functions of `src/internal/vg_rsa_pss_sha384_mgf1_sha384_encode_shani.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_sha384_mgf1_sha384_encode_shani:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+128], rdi
	mov QWORD PTR [rsp+136], rsi
	mov QWORD PTR [rsp+296], rdx
	mov QWORD PTR [rsp+312], rcx
	mov QWORD PTR [rsp+320], r8
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+136]
	shl rax, 3
	sub rax, r9
	mov rcx, rax
	mov eax, 255
	shr rax, cl
	mov QWORD PTR [rsp+200], rax
	mov eax, 0
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+136]
	cmp rax, 50
	jb 20f
	mov rdx, QWORD PTR [rsp+320]
	sub rax, 50
	cmp rax, rdx
	jb 22f
	add rax, 1
	mov QWORD PTR [rsp+192], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov rdx, QWORD PTR [rsp+208]
	add rax, rdx
	mov QWORD PTR [rsp+184], rax
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 24b
	mov rsi, QWORD PTR [rsp+296]
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+8], al
	add r8, 1
	cmp r8, 48
	jne 25b
	mov rsi, QWORD PTR [rsp+312]
	mov r10, QWORD PTR [rsp+320]
	mov r8d, 0
	test r10, r10
	je 26f
28:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+56], al
	add r8, 1
	cmp r8, r10
	jne 28b
	jmp 27f
26:
27:
	mov rax, QWORD PTR [rsp+320]
	add rax, 56
	mov QWORD PTR [rsp+216], rax
	add rax, 16
	shr rax, 7
	add rax, 1
	mov QWORD PTR [rsp+224], rax
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	call {vg_sha384_init}
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov rdx, QWORD PTR [rsp+216]
	mov r10, QWORD PTR [rsp+224]
	ror r10, 57
	mov r8d, 0
29:
	mov rax, r8
	xor rax, rdx
	cmp rax, 1
	sbb rax, rax
	and rax, 128
	movzx r9d, BYTE PTR [rcx+r8*1]
	or r9, rax
	mov BYTE PTR [rcx+r8*1], r9b
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rbx, QWORD PTR [rsp+168]
	add rbx, 2192
	mov r12, QWORD PTR [rsp+216]
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
	mov rax, QWORD PTR [rsp+216]
	add rax, 16
	shr rax, 7
	mov QWORD PTR [rsp+240], rax
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3696
	mov rsi, QWORD PTR [rsp+168]
	add rsi, 2368
	mov rdx, QWORD PTR [rsp+240]
	mov r10, QWORD PTR [rsp+224]
	mov r8d, 0
210:
	mov r11, r8
	xor r11, rdx
	cmp r11, 1
	sbb r11, r11
	mov r9d, 0
211:
	movzx eax, BYTE PTR [rsi+r9*1]
	and rax, r11
	movzx edi, BYTE PTR [rcx+r9*1]
	or rdi, rax
	mov BYTE PTR [rcx+r9*1], dil
	add r9, 1
	cmp r9, 16
	jne 211b
	add rcx, 128
	add r8, 1
	cmp r8, r10
	jne 210b
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
212:
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rcx, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+232]
	ror rsi, 57
	add rsi, rcx
	add rsi, 3584
	mov edx, 1
	call {vg_sha512_compress_shani}
	mov rcx, QWORD PTR [rsp+168]
	mov rax, QWORD PTR [rsp+232]
	xor rax, QWORD PTR [rsp+240]
	cmp rax, 1
	sbb r11, r11
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1+2048]
	movzx edx, BYTE PTR [rcx+r8*1+2240]
	xor rax, rdx
	and rax, r11
	xor rdx, rax
	mov BYTE PTR [rcx+r8*1+2240], dl
	add r8, 1
	cmp r8, 64
	jne 213b
	mov rax, QWORD PTR [rsp+232]
	add rax, 1
	mov QWORD PTR [rsp+232], rax
	mov rdx, QWORD PTR [rsp+224]
	cmp rax, rdx
	jne 212b
	mov rbx, QWORD PTR [rsp+168]
	add rbx, 2240
	mov rbp, QWORD PTR [rsp+168]
	add rbp, 2304
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
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 2560
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
214:
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 214b
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+192]
	add rdi, rax
	mov rax, QWORD PTR [rsp+320]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+312]
	mov r10, QWORD PTR [rsp+320]
	mov r8d, 0
	test r10, r10
	je 215f
217:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	jmp 216f
215:
216:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+192]
	add rdi, rax
	mov rsi, QWORD PTR [rsp+168]
	add rsi, 2304
	mov r8d, 0
218:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, 48
	jne 218b
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2560
	mov rax, QWORD PTR [rsp+136]
	add rdi, rax
	sub rdi, 1
	mov eax, 188
	mov BYTE PTR [rdi], al
	mov eax, 0
	mov QWORD PTR [rsp+248], rax
	mov QWORD PTR [rsp+256], rax
219:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov eax, 0
	mov r8d, 0
220:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 128
	jne 220b
	mov rsi, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	add rsi, r8
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rcx+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rcx+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rcx+24], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rcx+32], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rcx+40], rax
	mov rax, QWORD PTR [rsp+248]
	mov BYTE PTR [rcx+51], al
	shr rax, 8
	mov BYTE PTR [rcx+50], al
	shr rax, 8
	mov BYTE PTR [rcx+49], al
	shr rax, 8
	mov BYTE PTR [rcx+48], al
	mov eax, 52
	mov QWORD PTR [rsp+216], rax
	mov eax, 1
	mov QWORD PTR [rsp+224], rax
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	call {vg_sha384_init}
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	movzx eax, BYTE PTR [rcx+52]
	or rax, 128
	mov BYTE PTR [rcx+52], al
	mov rbx, QWORD PTR [rsp+168]
	add rbx, 2192
	mov r12, QWORD PTR [rsp+216]
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
	mov rax, QWORD PTR [rsp+216]
	add rax, 16
	shr rax, 7
	mov QWORD PTR [rsp+240], rax
	mov rsi, QWORD PTR [rsp+168]
	add rsi, 2368
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3696
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rcx+8], rax
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rcx, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+232]
	ror rsi, 57
	add rsi, rcx
	add rsi, 3584
	mov edx, 1
	call {vg_sha512_compress_shani}
	mov rbx, QWORD PTR [rsp+168]
	add rbx, 2048
	mov rbp, QWORD PTR [rsp+168]
	add rbp, 2304
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
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 2304
	mov rdx, QWORD PTR [rsp+256]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+192]
	sub rax, rdx
	mov r10d, 48
	cmp rax, r10
	jb 221f
	mov rax, QWORD PTR [rcx]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rcx+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rcx+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rcx+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rcx+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rcx+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	jmp 222f
221:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 2304
	mov rdx, QWORD PTR [rsp+256]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+192]
	sub rax, rdx
	mov r10d, 48
	cmp rax, r10
	jb 223f
	jmp 224f
223:
	mov r10, rax
224:
	mov r8d, 0
225:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 225b
222:
	mov rax, QWORD PTR [rsp+248]
	add rax, 1
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+256]
	add rax, 48
	mov QWORD PTR [rsp+256], rax
	mov rdx, QWORD PTR [rsp+192]
	cmp rax, rdx
	jb 219b
	mov rdi, QWORD PTR [rsp+184]
	movzx eax, BYTE PTR [rdi]
	and rax, QWORD PTR [rsp+200]
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+168]
	add rsi, 2560
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov r8d, 0
226:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 226b
	mov eax, 1
	jmp 23f
22:
	mov eax, 0
23:
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
