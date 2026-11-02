// The functions of `src/internal/vg_rsa_pss_sha224_mgf1_sha224_encode.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_sha224_mgf1_sha224_encode:
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
	cmp rax, 30
	jb 20f
	mov rdx, QWORD PTR [rsp+320]
	sub rax, 30
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
	cmp r8, 28
	jne 25b
	mov rsi, QWORD PTR [rsp+312]
	mov r10, QWORD PTR [rsp+320]
	mov r8d, 0
	test r10, r10
	je 26f
28:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+36], al
	add r8, 1
	cmp r8, r10
	jne 28b
	jmp 27f
26:
27:
	mov rax, QWORD PTR [rsp+320]
	add rax, 36
	mov QWORD PTR [rsp+216], rax
	add rax, 8
	shr rax, 6
	add rax, 1
	mov QWORD PTR [rsp+224], rax
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	call {vg_sha224_init}
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov rdx, QWORD PTR [rsp+216]
	mov r10, QWORD PTR [rsp+224]
	ror r10, 58
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
	add rbx, 2280
	mov r12, QWORD PTR [rsp+216]
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
	mov rax, QWORD PTR [rsp+216]
	add rax, 8
	shr rax, 6
	mov QWORD PTR [rsp+240], rax
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3640
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
	cmp r9, 8
	jne 211b
	add rcx, 64
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
	ror rsi, 58
	add rsi, rcx
	add rsi, 3584
	mov edx, 1
	call {vg_sha256_compress}
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
	cmp r8, 32
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
	cmp r8, 28
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
	cmp r8, 64
	jne 220b
	mov rsi, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	add rsi, r8
	mov r8d, 0
221:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 28
	jne 221b
	mov rax, QWORD PTR [rsp+248]
	mov BYTE PTR [rcx+31], al
	shr rax, 8
	mov BYTE PTR [rcx+30], al
	shr rax, 8
	mov BYTE PTR [rcx+29], al
	shr rax, 8
	mov BYTE PTR [rcx+28], al
	mov eax, 32
	mov QWORD PTR [rsp+216], rax
	mov eax, 1
	mov QWORD PTR [rsp+224], rax
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	call {vg_sha224_init}
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	movzx eax, BYTE PTR [rcx+32]
	or rax, 128
	mov BYTE PTR [rcx+32], al
	mov rbx, QWORD PTR [rsp+168]
	add rbx, 2280
	mov r12, QWORD PTR [rsp+216]
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
	mov rax, QWORD PTR [rsp+216]
	add rax, 8
	shr rax, 6
	mov QWORD PTR [rsp+240], rax
	mov rsi, QWORD PTR [rsp+168]
	add rsi, 2368
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3640
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rcx], rax
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rcx, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+232]
	ror rsi, 58
	add rsi, rcx
	add rsi, 3584
	mov edx, 1
	call {vg_sha256_compress}
	mov rbx, QWORD PTR [rsp+168]
	add rbx, 2048
	mov rbp, QWORD PTR [rsp+168]
	add rbp, 2304
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
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 2304
	mov rdx, QWORD PTR [rsp+256]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+192]
	sub rax, rdx
	mov r10d, 28
	cmp rax, r10
	jb 222f
	jmp 223f
222:
	mov r10, rax
223:
	mov r8d, 0
224:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 224b
	mov rax, QWORD PTR [rsp+248]
	add rax, 1
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+256]
	add rax, 28
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
225:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 225b
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
