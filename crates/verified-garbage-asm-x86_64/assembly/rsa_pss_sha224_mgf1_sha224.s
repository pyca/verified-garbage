// The functions of `src/rsa_pss_sha224_mgf1_sha224.rs` of `verified-garbage-asm-x86_64`, as text: generated from
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

vg_rsa_pss_sha224_mgf1_sha224_check_encoding:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+296], rdi
	mov QWORD PTR [rsp+304], rsi
	mov QWORD PTR [rsp+136], rdx
	mov QWORD PTR [rsp+288], r8
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+136]
	shl rax, 3
	sub rax, rcx
	mov rcx, rax
	mov eax, 255
	shr rax, cl
	mov QWORD PTR [rsp+200], rax
	mov eax, 0
	mov QWORD PTR [rsp+208], rax
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 2560
	mov rsi, QWORD PTR [rsp+304]
	mov r10, QWORD PTR [rsp+136]
	mov r8d, 0
20:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 20b
	mov eax, r9d
	test rax, rax
	je 21f
	mov eax, 1
	mov QWORD PTR [rsp+280], rax
	mov edx, 0
	jmp 22f
21:
	mov eax, 0
	mov QWORD PTR [rsp+280], rax
	mov rdx, QWORD PTR [rsp+288]
22:
	mov rax, QWORD PTR [rsp+136]
	cmp rax, 30
	jb 23f
	mov rax, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+208]
	sub rax, r8
	sub rax, 30
	cmp rax, rdx
	jb 25f
	add rax, 1
	mov QWORD PTR [rsp+192], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov rdx, QWORD PTR [rsp+208]
	add rax, rdx
	mov QWORD PTR [rsp+184], rax
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 2560
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rcx
	sub rdi, 1
	movzx eax, BYTE PTR [rdi]
	xor rax, 188
	movzx r9d, BYTE PTR [rcx]
	mov r10, QWORD PTR [rsp+208]
	mov r11d, 0
	sub r11, r10
	and r9, r11
	or rax, r9
	mov rdi, QWORD PTR [rsp+184]
	movzx r9d, BYTE PTR [rdi]
	mov r11, QWORD PTR [rsp+200]
	xor r11, 255
	and r9, r11
	or rax, r9
	mov QWORD PTR [rsp+264], rax
	mov eax, 0
	mov QWORD PTR [rsp+248], rax
	mov QWORD PTR [rsp+256], rax
27:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov eax, 0
	mov r8d, 0
28:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 64
	jne 28b
	mov rsi, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	add rsi, r8
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 28
	jne 29b
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
	jb 210f
	jmp 211f
210:
	mov r10, rax
211:
	mov r8d, 0
212:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 212b
	mov rax, QWORD PTR [rsp+248]
	add rax, 1
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+256]
	add rax, 28
	mov QWORD PTR [rsp+256], rax
	mov rdx, QWORD PTR [rsp+192]
	cmp rax, rdx
	jb 27b
	mov rdi, QWORD PTR [rsp+184]
	movzx eax, BYTE PTR [rdi]
	and rax, QWORD PTR [rsp+200]
	mov BYTE PTR [rdi], al
	mov rax, QWORD PTR [rsp+280]
	test rax, rax
	je 213f
	mov rdi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
	mov edx, 0
	mov esi, 0
	mov r11d, 0
215:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	xor r9, -1
	mov rcx, rdx
	xor rcx, -1
	and r9, rcx
	mov rcx, r8
	and rcx, r9
	or rsi, rcx
	and rax, r9
	or r11, rax
	or rdx, r9
	add r8, 1
	cmp r8, r10
	jne 215b
	xor r11, 1
	xor rdx, -1
	or r11, rdx
	mov rax, QWORD PTR [rsp+264]
	or rax, r11
	mov QWORD PTR [rsp+272], rsi
	mov rcx, QWORD PTR [rsp+192]
	sub rcx, rsi
	sub rcx, 1
	mov r9, QWORD PTR [rsp+280]
	test r9, r9
	je 216f
	jmp 217f
216:
	mov r9, rcx
	xor r9, QWORD PTR [rsp+288]
	or rax, r9
217:
	mov QWORD PTR [rsp+264], rax
	add rcx, 36
	mov QWORD PTR [rsp+216], rcx
	jmp 214f
213:
	mov rax, QWORD PTR [rsp+288]
	cmp rax, QWORD PTR [rsp+192]
	jb 218f
	mov rdi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
	mov edx, 0
	mov esi, 0
	mov r11d, 0
220:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	xor r9, -1
	mov rcx, rdx
	xor rcx, -1
	and r9, rcx
	mov rcx, r8
	and rcx, r9
	or rsi, rcx
	and rax, r9
	or r11, rax
	or rdx, r9
	add r8, 1
	cmp r8, r10
	jne 220b
	xor r11, 1
	xor rdx, -1
	or r11, rdx
	mov rax, QWORD PTR [rsp+264]
	or rax, r11
	mov QWORD PTR [rsp+272], rsi
	mov rcx, QWORD PTR [rsp+192]
	sub rcx, rsi
	sub rcx, 1
	mov r9, QWORD PTR [rsp+280]
	test r9, r9
	je 221f
	jmp 222f
221:
	mov r9, rcx
	xor r9, QWORD PTR [rsp+288]
	or rax, r9
222:
	mov QWORD PTR [rsp+264], rax
	add rcx, 36
	mov QWORD PTR [rsp+216], rcx
	jmp 219f
218:
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+192]
	mov rdx, QWORD PTR [rsp+288]
	sub rsi, rdx
	sub rsi, 1
	mov rcx, rsi
	shr rcx, 3
	shl rcx, 3
	mov rax, QWORD PTR [rsp+264]
	mov r8d, 0
	test rcx, rcx
	je 223f
225:
	or rax, QWORD PTR [rdi+r8*1]
	add r8, 8
	cmp r8, rcx
	jne 225b
	jmp 224f
223:
224:
	cmp r8, rsi
	je 226f
228:
	movzx edx, BYTE PTR [rdi+r8*1]
	or rax, rdx
	add r8, 1
	cmp r8, rsi
	jne 228b
	jmp 227f
226:
227:
	movzx edx, BYTE PTR [rdi+rsi*1]
	xor rdx, 1
	or rax, rdx
	mov QWORD PTR [rsp+272], rsi
	mov QWORD PTR [rsp+264], rax
	mov rax, QWORD PTR [rsp+288]
	add rax, 36
	mov QWORD PTR [rsp+216], rax
219:
214:
	mov rax, QWORD PTR [rsp+280]
	test rax, rax
	je 229f
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov eax, 0
	mov r8d, 0
231:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 231b
	mov rsi, QWORD PTR [rsp+296]
	mov r8d, 0
232:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+8], al
	add r8, 1
	cmp r8, 28
	jne 232b
	mov rsi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
233:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+36], al
	add r8, 1
	cmp r8, r10
	jne 233b
	mov rax, QWORD PTR [rsp+272]
	add rax, 1
	mov QWORD PTR [rsp+360], rax
	mov eax, 1
	mov QWORD PTR [rsp+368], rax
	mov eax, 10
	mov QWORD PTR [rsp+352], rax
234:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3620
	mov rsi, QWORD PTR [rsp+368]
	add rsi, rcx
	mov r11, QWORD PTR [rsp+360]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
235:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 235b
	mov rax, QWORD PTR [rsp+360]
	shr rax, 1
	mov QWORD PTR [rsp+360], rax
	mov rax, QWORD PTR [rsp+368]
	add rax, rax
	mov QWORD PTR [rsp+368], rax
	mov rax, QWORD PTR [rsp+352]
	sub rax, 1
	mov QWORD PTR [rsp+352], rax
	jne 234b
	mov rax, QWORD PTR [rsp+192]
	add rax, 43
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
236:
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
	jne 236b
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
237:
	mov r11, r8
	xor r11, rdx
	cmp r11, 1
	sbb r11, r11
	mov r9d, 0
238:
	movzx eax, BYTE PTR [rsi+r9*1]
	and rax, r11
	movzx edi, BYTE PTR [rcx+r9*1]
	or rdi, rax
	mov BYTE PTR [rcx+r9*1], dil
	add r9, 1
	cmp r9, 8
	jne 238b
	add rcx, 64
	add r8, 1
	cmp r8, r10
	jne 237b
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
239:
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
240:
	movzx eax, BYTE PTR [rcx+r8*1+2048]
	movzx edx, BYTE PTR [rcx+r8*1+2240]
	xor rax, rdx
	and rax, r11
	xor rdx, rax
	mov BYTE PTR [rcx+r8*1+2240], dl
	add r8, 1
	cmp r8, 32
	jne 240b
	mov rax, QWORD PTR [rsp+232]
	add rax, 1
	mov QWORD PTR [rsp+232], rax
	mov rdx, QWORD PTR [rsp+224]
	cmp rax, rdx
	jne 239b
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
	add rcx, 2304
	mov rdi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+192]
	add rdi, rdx
	mov rdx, QWORD PTR [rsp+264]
	mov r8d, 0
241:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 28
	jne 241b
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
	jmp 230f
229:
	mov rax, QWORD PTR [rsp+288]
	cmp rax, QWORD PTR [rsp+192]
	jb 242f
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov eax, 0
	mov r8d, 0
244:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 244b
	mov rsi, QWORD PTR [rsp+296]
	mov r8d, 0
245:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+8], al
	add r8, 1
	cmp r8, 28
	jne 245b
	mov rsi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
246:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+36], al
	add r8, 1
	cmp r8, r10
	jne 246b
	mov rax, QWORD PTR [rsp+272]
	add rax, 1
	mov QWORD PTR [rsp+360], rax
	mov eax, 1
	mov QWORD PTR [rsp+368], rax
	mov eax, 10
	mov QWORD PTR [rsp+352], rax
247:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3620
	mov rsi, QWORD PTR [rsp+368]
	add rsi, rcx
	mov r11, QWORD PTR [rsp+360]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
248:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 248b
	mov rax, QWORD PTR [rsp+360]
	shr rax, 1
	mov QWORD PTR [rsp+360], rax
	mov rax, QWORD PTR [rsp+368]
	add rax, rax
	mov QWORD PTR [rsp+368], rax
	mov rax, QWORD PTR [rsp+352]
	sub rax, 1
	mov QWORD PTR [rsp+352], rax
	jne 247b
	mov rax, QWORD PTR [rsp+192]
	add rax, 43
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
249:
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
	jne 249b
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
250:
	mov r11, r8
	xor r11, rdx
	cmp r11, 1
	sbb r11, r11
	mov r9d, 0
251:
	movzx eax, BYTE PTR [rsi+r9*1]
	and rax, r11
	movzx edi, BYTE PTR [rcx+r9*1]
	or rdi, rax
	mov BYTE PTR [rcx+r9*1], dil
	add r9, 1
	cmp r9, 8
	jne 251b
	add rcx, 64
	add r8, 1
	cmp r8, r10
	jne 250b
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
252:
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
253:
	movzx eax, BYTE PTR [rcx+r8*1+2048]
	movzx edx, BYTE PTR [rcx+r8*1+2240]
	xor rax, rdx
	and rax, r11
	xor rdx, rax
	mov BYTE PTR [rcx+r8*1+2240], dl
	add r8, 1
	cmp r8, 32
	jne 253b
	mov rax, QWORD PTR [rsp+232]
	add rax, 1
	mov QWORD PTR [rsp+232], rax
	mov rdx, QWORD PTR [rsp+224]
	cmp rax, rdx
	jne 252b
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
	add rcx, 2304
	mov rdi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+192]
	add rdi, rdx
	mov rdx, QWORD PTR [rsp+264]
	mov r8d, 0
254:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 28
	jne 254b
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
	jmp 243f
242:
	mov rax, QWORD PTR [rsp+288]
	add rax, 36
	mov QWORD PTR [rsp+216], rax
	add rax, 8
	shr rax, 6
	add rax, 1
	mov QWORD PTR [rsp+224], rax
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov r10, QWORD PTR [rsp+224]
	ror r10, 58
	mov eax, 0
	mov r8d, 0
255:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, r10
	jne 255b
	mov rsi, QWORD PTR [rsp+296]
	mov r8d, 0
256:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+8], al
	add r8, 1
	cmp r8, 28
	jne 256b
	mov rsi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+192]
	add rsi, rax
	mov r10, QWORD PTR [rsp+288]
	sub rsi, r10
	mov r8d, 0
	test r10, r10
	je 257f
259:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+36], al
	add r8, 1
	cmp r8, r10
	jne 259b
	jmp 258f
257:
258:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov rdx, QWORD PTR [rsp+288]
	mov eax, 128
	mov BYTE PTR [rcx+rdx*1+36], al
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	call {vg_sha224_init}
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
	mov rax, QWORD PTR [rsp+224]
	ror rax, 58
	add rcx, rax
	add rcx, 3576
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rcx], rax
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
260:
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rcx, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+232]
	ror rsi, 58
	add rsi, rcx
	add rsi, 3584
	mov edx, 1
	call {vg_sha256_compress}
	mov rax, QWORD PTR [rsp+232]
	add rax, 1
	mov QWORD PTR [rsp+232], rax
	mov rdx, QWORD PTR [rsp+224]
	cmp rax, rdx
	jne 260b
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
	mov rdi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+192]
	add rdi, rdx
	mov rdx, QWORD PTR [rsp+264]
	mov r8d, 0
261:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 28
	jne 261b
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
243:
230:
	jmp 26f
25:
	mov eax, 0
26:
	jmp 24f
23:
	mov eax, 0
24:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_encode_avx2:
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
	call {vg_sha256_compress_avx2}
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
	call {vg_sha256_compress_avx2}
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

vg_rsa_pss_sha224_mgf1_sha224_check_encoding_avx2:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+296], rdi
	mov QWORD PTR [rsp+304], rsi
	mov QWORD PTR [rsp+136], rdx
	mov QWORD PTR [rsp+288], r8
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+136]
	shl rax, 3
	sub rax, rcx
	mov rcx, rax
	mov eax, 255
	shr rax, cl
	mov QWORD PTR [rsp+200], rax
	mov eax, 0
	mov QWORD PTR [rsp+208], rax
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 2560
	mov rsi, QWORD PTR [rsp+304]
	mov r10, QWORD PTR [rsp+136]
	mov r8d, 0
20:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 20b
	mov eax, r9d
	test rax, rax
	je 21f
	mov eax, 1
	mov QWORD PTR [rsp+280], rax
	mov edx, 0
	jmp 22f
21:
	mov eax, 0
	mov QWORD PTR [rsp+280], rax
	mov rdx, QWORD PTR [rsp+288]
22:
	mov rax, QWORD PTR [rsp+136]
	cmp rax, 30
	jb 23f
	mov rax, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+208]
	sub rax, r8
	sub rax, 30
	cmp rax, rdx
	jb 25f
	add rax, 1
	mov QWORD PTR [rsp+192], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov rdx, QWORD PTR [rsp+208]
	add rax, rdx
	mov QWORD PTR [rsp+184], rax
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 2560
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rcx
	sub rdi, 1
	movzx eax, BYTE PTR [rdi]
	xor rax, 188
	movzx r9d, BYTE PTR [rcx]
	mov r10, QWORD PTR [rsp+208]
	mov r11d, 0
	sub r11, r10
	and r9, r11
	or rax, r9
	mov rdi, QWORD PTR [rsp+184]
	movzx r9d, BYTE PTR [rdi]
	mov r11, QWORD PTR [rsp+200]
	xor r11, 255
	and r9, r11
	or rax, r9
	mov QWORD PTR [rsp+264], rax
	mov eax, 0
	mov QWORD PTR [rsp+248], rax
	mov QWORD PTR [rsp+256], rax
27:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov eax, 0
	mov r8d, 0
28:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 64
	jne 28b
	mov rsi, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	add rsi, r8
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 28
	jne 29b
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
	call {vg_sha256_compress_avx2}
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
	jb 210f
	jmp 211f
210:
	mov r10, rax
211:
	mov r8d, 0
212:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 212b
	mov rax, QWORD PTR [rsp+248]
	add rax, 1
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+256]
	add rax, 28
	mov QWORD PTR [rsp+256], rax
	mov rdx, QWORD PTR [rsp+192]
	cmp rax, rdx
	jb 27b
	mov rdi, QWORD PTR [rsp+184]
	movzx eax, BYTE PTR [rdi]
	and rax, QWORD PTR [rsp+200]
	mov BYTE PTR [rdi], al
	mov rax, QWORD PTR [rsp+280]
	test rax, rax
	je 213f
	mov rdi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
	mov edx, 0
	mov esi, 0
	mov r11d, 0
215:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	xor r9, -1
	mov rcx, rdx
	xor rcx, -1
	and r9, rcx
	mov rcx, r8
	and rcx, r9
	or rsi, rcx
	and rax, r9
	or r11, rax
	or rdx, r9
	add r8, 1
	cmp r8, r10
	jne 215b
	xor r11, 1
	xor rdx, -1
	or r11, rdx
	mov rax, QWORD PTR [rsp+264]
	or rax, r11
	mov QWORD PTR [rsp+272], rsi
	mov rcx, QWORD PTR [rsp+192]
	sub rcx, rsi
	sub rcx, 1
	mov r9, QWORD PTR [rsp+280]
	test r9, r9
	je 216f
	jmp 217f
216:
	mov r9, rcx
	xor r9, QWORD PTR [rsp+288]
	or rax, r9
217:
	mov QWORD PTR [rsp+264], rax
	add rcx, 36
	mov QWORD PTR [rsp+216], rcx
	jmp 214f
213:
	mov rax, QWORD PTR [rsp+288]
	cmp rax, QWORD PTR [rsp+192]
	jb 218f
	mov rdi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
	mov edx, 0
	mov esi, 0
	mov r11d, 0
220:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	xor r9, -1
	mov rcx, rdx
	xor rcx, -1
	and r9, rcx
	mov rcx, r8
	and rcx, r9
	or rsi, rcx
	and rax, r9
	or r11, rax
	or rdx, r9
	add r8, 1
	cmp r8, r10
	jne 220b
	xor r11, 1
	xor rdx, -1
	or r11, rdx
	mov rax, QWORD PTR [rsp+264]
	or rax, r11
	mov QWORD PTR [rsp+272], rsi
	mov rcx, QWORD PTR [rsp+192]
	sub rcx, rsi
	sub rcx, 1
	mov r9, QWORD PTR [rsp+280]
	test r9, r9
	je 221f
	jmp 222f
221:
	mov r9, rcx
	xor r9, QWORD PTR [rsp+288]
	or rax, r9
222:
	mov QWORD PTR [rsp+264], rax
	add rcx, 36
	mov QWORD PTR [rsp+216], rcx
	jmp 219f
218:
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+192]
	mov rdx, QWORD PTR [rsp+288]
	sub rsi, rdx
	sub rsi, 1
	mov rcx, rsi
	shr rcx, 3
	shl rcx, 3
	mov rax, QWORD PTR [rsp+264]
	mov r8d, 0
	test rcx, rcx
	je 223f
225:
	or rax, QWORD PTR [rdi+r8*1]
	add r8, 8
	cmp r8, rcx
	jne 225b
	jmp 224f
223:
224:
	cmp r8, rsi
	je 226f
228:
	movzx edx, BYTE PTR [rdi+r8*1]
	or rax, rdx
	add r8, 1
	cmp r8, rsi
	jne 228b
	jmp 227f
226:
227:
	movzx edx, BYTE PTR [rdi+rsi*1]
	xor rdx, 1
	or rax, rdx
	mov QWORD PTR [rsp+272], rsi
	mov QWORD PTR [rsp+264], rax
	mov rax, QWORD PTR [rsp+288]
	add rax, 36
	mov QWORD PTR [rsp+216], rax
219:
214:
	mov rax, QWORD PTR [rsp+280]
	test rax, rax
	je 229f
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov eax, 0
	mov r8d, 0
231:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 231b
	mov rsi, QWORD PTR [rsp+296]
	mov r8d, 0
232:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+8], al
	add r8, 1
	cmp r8, 28
	jne 232b
	mov rsi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
233:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+36], al
	add r8, 1
	cmp r8, r10
	jne 233b
	mov rax, QWORD PTR [rsp+272]
	add rax, 1
	mov QWORD PTR [rsp+360], rax
	mov eax, 1
	mov QWORD PTR [rsp+368], rax
	mov eax, 10
	mov QWORD PTR [rsp+352], rax
234:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3620
	mov rsi, QWORD PTR [rsp+368]
	add rsi, rcx
	mov r11, QWORD PTR [rsp+360]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
235:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 235b
	mov rax, QWORD PTR [rsp+360]
	shr rax, 1
	mov QWORD PTR [rsp+360], rax
	mov rax, QWORD PTR [rsp+368]
	add rax, rax
	mov QWORD PTR [rsp+368], rax
	mov rax, QWORD PTR [rsp+352]
	sub rax, 1
	mov QWORD PTR [rsp+352], rax
	jne 234b
	mov rax, QWORD PTR [rsp+192]
	add rax, 43
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
236:
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
	jne 236b
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
237:
	mov r11, r8
	xor r11, rdx
	cmp r11, 1
	sbb r11, r11
	mov r9d, 0
238:
	movzx eax, BYTE PTR [rsi+r9*1]
	and rax, r11
	movzx edi, BYTE PTR [rcx+r9*1]
	or rdi, rax
	mov BYTE PTR [rcx+r9*1], dil
	add r9, 1
	cmp r9, 8
	jne 238b
	add rcx, 64
	add r8, 1
	cmp r8, r10
	jne 237b
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
239:
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rcx, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+232]
	ror rsi, 58
	add rsi, rcx
	add rsi, 3584
	mov edx, 1
	call {vg_sha256_compress_avx2}
	mov rcx, QWORD PTR [rsp+168]
	mov rax, QWORD PTR [rsp+232]
	xor rax, QWORD PTR [rsp+240]
	cmp rax, 1
	sbb r11, r11
	mov r8d, 0
240:
	movzx eax, BYTE PTR [rcx+r8*1+2048]
	movzx edx, BYTE PTR [rcx+r8*1+2240]
	xor rax, rdx
	and rax, r11
	xor rdx, rax
	mov BYTE PTR [rcx+r8*1+2240], dl
	add r8, 1
	cmp r8, 32
	jne 240b
	mov rax, QWORD PTR [rsp+232]
	add rax, 1
	mov QWORD PTR [rsp+232], rax
	mov rdx, QWORD PTR [rsp+224]
	cmp rax, rdx
	jne 239b
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
	add rcx, 2304
	mov rdi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+192]
	add rdi, rdx
	mov rdx, QWORD PTR [rsp+264]
	mov r8d, 0
241:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 28
	jne 241b
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
	jmp 230f
229:
	mov rax, QWORD PTR [rsp+288]
	cmp rax, QWORD PTR [rsp+192]
	jb 242f
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov eax, 0
	mov r8d, 0
244:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 244b
	mov rsi, QWORD PTR [rsp+296]
	mov r8d, 0
245:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+8], al
	add r8, 1
	cmp r8, 28
	jne 245b
	mov rsi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
246:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+36], al
	add r8, 1
	cmp r8, r10
	jne 246b
	mov rax, QWORD PTR [rsp+272]
	add rax, 1
	mov QWORD PTR [rsp+360], rax
	mov eax, 1
	mov QWORD PTR [rsp+368], rax
	mov eax, 10
	mov QWORD PTR [rsp+352], rax
247:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3620
	mov rsi, QWORD PTR [rsp+368]
	add rsi, rcx
	mov r11, QWORD PTR [rsp+360]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
248:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 248b
	mov rax, QWORD PTR [rsp+360]
	shr rax, 1
	mov QWORD PTR [rsp+360], rax
	mov rax, QWORD PTR [rsp+368]
	add rax, rax
	mov QWORD PTR [rsp+368], rax
	mov rax, QWORD PTR [rsp+352]
	sub rax, 1
	mov QWORD PTR [rsp+352], rax
	jne 247b
	mov rax, QWORD PTR [rsp+192]
	add rax, 43
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
249:
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
	jne 249b
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
250:
	mov r11, r8
	xor r11, rdx
	cmp r11, 1
	sbb r11, r11
	mov r9d, 0
251:
	movzx eax, BYTE PTR [rsi+r9*1]
	and rax, r11
	movzx edi, BYTE PTR [rcx+r9*1]
	or rdi, rax
	mov BYTE PTR [rcx+r9*1], dil
	add r9, 1
	cmp r9, 8
	jne 251b
	add rcx, 64
	add r8, 1
	cmp r8, r10
	jne 250b
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
252:
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rcx, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+232]
	ror rsi, 58
	add rsi, rcx
	add rsi, 3584
	mov edx, 1
	call {vg_sha256_compress_avx2}
	mov rcx, QWORD PTR [rsp+168]
	mov rax, QWORD PTR [rsp+232]
	xor rax, QWORD PTR [rsp+240]
	cmp rax, 1
	sbb r11, r11
	mov r8d, 0
253:
	movzx eax, BYTE PTR [rcx+r8*1+2048]
	movzx edx, BYTE PTR [rcx+r8*1+2240]
	xor rax, rdx
	and rax, r11
	xor rdx, rax
	mov BYTE PTR [rcx+r8*1+2240], dl
	add r8, 1
	cmp r8, 32
	jne 253b
	mov rax, QWORD PTR [rsp+232]
	add rax, 1
	mov QWORD PTR [rsp+232], rax
	mov rdx, QWORD PTR [rsp+224]
	cmp rax, rdx
	jne 252b
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
	add rcx, 2304
	mov rdi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+192]
	add rdi, rdx
	mov rdx, QWORD PTR [rsp+264]
	mov r8d, 0
254:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 28
	jne 254b
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
	jmp 243f
242:
	mov rax, QWORD PTR [rsp+288]
	add rax, 36
	mov QWORD PTR [rsp+216], rax
	add rax, 8
	shr rax, 6
	add rax, 1
	mov QWORD PTR [rsp+224], rax
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov r10, QWORD PTR [rsp+224]
	ror r10, 58
	mov eax, 0
	mov r8d, 0
255:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, r10
	jne 255b
	mov rsi, QWORD PTR [rsp+296]
	mov r8d, 0
256:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+8], al
	add r8, 1
	cmp r8, 28
	jne 256b
	mov rsi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+192]
	add rsi, rax
	mov r10, QWORD PTR [rsp+288]
	sub rsi, r10
	mov r8d, 0
	test r10, r10
	je 257f
259:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+36], al
	add r8, 1
	cmp r8, r10
	jne 259b
	jmp 258f
257:
258:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov rdx, QWORD PTR [rsp+288]
	mov eax, 128
	mov BYTE PTR [rcx+rdx*1+36], al
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	call {vg_sha224_init}
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
	mov rax, QWORD PTR [rsp+224]
	ror rax, 58
	add rcx, rax
	add rcx, 3576
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rcx], rax
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
260:
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rcx, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+232]
	ror rsi, 58
	add rsi, rcx
	add rsi, 3584
	mov edx, 1
	call {vg_sha256_compress_avx2}
	mov rax, QWORD PTR [rsp+232]
	add rax, 1
	mov QWORD PTR [rsp+232], rax
	mov rdx, QWORD PTR [rsp+224]
	cmp rax, rdx
	jne 260b
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
	mov rdi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+192]
	add rdi, rdx
	mov rdx, QWORD PTR [rsp+264]
	mov r8d, 0
261:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 28
	jne 261b
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
243:
230:
	jmp 26f
25:
	mov eax, 0
26:
	jmp 24f
23:
	mov eax, 0
24:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_sha224_mgf1_sha224_encode_shani:
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
	call {vg_sha256_compress_shani}
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
	call {vg_sha256_compress_shani}
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

vg_rsa_pss_sha224_mgf1_sha224_check_encoding_shani:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+296], rdi
	mov QWORD PTR [rsp+304], rsi
	mov QWORD PTR [rsp+136], rdx
	mov QWORD PTR [rsp+288], r8
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+136]
	shl rax, 3
	sub rax, rcx
	mov rcx, rax
	mov eax, 255
	shr rax, cl
	mov QWORD PTR [rsp+200], rax
	mov eax, 0
	mov QWORD PTR [rsp+208], rax
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 2560
	mov rsi, QWORD PTR [rsp+304]
	mov r10, QWORD PTR [rsp+136]
	mov r8d, 0
20:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 20b
	mov eax, r9d
	test rax, rax
	je 21f
	mov eax, 1
	mov QWORD PTR [rsp+280], rax
	mov edx, 0
	jmp 22f
21:
	mov eax, 0
	mov QWORD PTR [rsp+280], rax
	mov rdx, QWORD PTR [rsp+288]
22:
	mov rax, QWORD PTR [rsp+136]
	cmp rax, 30
	jb 23f
	mov rax, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+208]
	sub rax, r8
	sub rax, 30
	cmp rax, rdx
	jb 25f
	add rax, 1
	mov QWORD PTR [rsp+192], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov rdx, QWORD PTR [rsp+208]
	add rax, rdx
	mov QWORD PTR [rsp+184], rax
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 2560
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rcx
	sub rdi, 1
	movzx eax, BYTE PTR [rdi]
	xor rax, 188
	movzx r9d, BYTE PTR [rcx]
	mov r10, QWORD PTR [rsp+208]
	mov r11d, 0
	sub r11, r10
	and r9, r11
	or rax, r9
	mov rdi, QWORD PTR [rsp+184]
	movzx r9d, BYTE PTR [rdi]
	mov r11, QWORD PTR [rsp+200]
	xor r11, 255
	and r9, r11
	or rax, r9
	mov QWORD PTR [rsp+264], rax
	mov eax, 0
	mov QWORD PTR [rsp+248], rax
	mov QWORD PTR [rsp+256], rax
27:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov eax, 0
	mov r8d, 0
28:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 64
	jne 28b
	mov rsi, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	add rsi, r8
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 28
	jne 29b
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
	call {vg_sha256_compress_shani}
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
	jb 210f
	jmp 211f
210:
	mov r10, rax
211:
	mov r8d, 0
212:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 212b
	mov rax, QWORD PTR [rsp+248]
	add rax, 1
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+256]
	add rax, 28
	mov QWORD PTR [rsp+256], rax
	mov rdx, QWORD PTR [rsp+192]
	cmp rax, rdx
	jb 27b
	mov rdi, QWORD PTR [rsp+184]
	movzx eax, BYTE PTR [rdi]
	and rax, QWORD PTR [rsp+200]
	mov BYTE PTR [rdi], al
	mov rax, QWORD PTR [rsp+280]
	test rax, rax
	je 213f
	mov rdi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
	mov edx, 0
	mov esi, 0
	mov r11d, 0
215:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	xor r9, -1
	mov rcx, rdx
	xor rcx, -1
	and r9, rcx
	mov rcx, r8
	and rcx, r9
	or rsi, rcx
	and rax, r9
	or r11, rax
	or rdx, r9
	add r8, 1
	cmp r8, r10
	jne 215b
	xor r11, 1
	xor rdx, -1
	or r11, rdx
	mov rax, QWORD PTR [rsp+264]
	or rax, r11
	mov QWORD PTR [rsp+272], rsi
	mov rcx, QWORD PTR [rsp+192]
	sub rcx, rsi
	sub rcx, 1
	mov r9, QWORD PTR [rsp+280]
	test r9, r9
	je 216f
	jmp 217f
216:
	mov r9, rcx
	xor r9, QWORD PTR [rsp+288]
	or rax, r9
217:
	mov QWORD PTR [rsp+264], rax
	add rcx, 36
	mov QWORD PTR [rsp+216], rcx
	jmp 214f
213:
	mov rax, QWORD PTR [rsp+288]
	cmp rax, QWORD PTR [rsp+192]
	jb 218f
	mov rdi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
	mov edx, 0
	mov esi, 0
	mov r11d, 0
220:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	xor r9, -1
	mov rcx, rdx
	xor rcx, -1
	and r9, rcx
	mov rcx, r8
	and rcx, r9
	or rsi, rcx
	and rax, r9
	or r11, rax
	or rdx, r9
	add r8, 1
	cmp r8, r10
	jne 220b
	xor r11, 1
	xor rdx, -1
	or r11, rdx
	mov rax, QWORD PTR [rsp+264]
	or rax, r11
	mov QWORD PTR [rsp+272], rsi
	mov rcx, QWORD PTR [rsp+192]
	sub rcx, rsi
	sub rcx, 1
	mov r9, QWORD PTR [rsp+280]
	test r9, r9
	je 221f
	jmp 222f
221:
	mov r9, rcx
	xor r9, QWORD PTR [rsp+288]
	or rax, r9
222:
	mov QWORD PTR [rsp+264], rax
	add rcx, 36
	mov QWORD PTR [rsp+216], rcx
	jmp 219f
218:
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+192]
	mov rdx, QWORD PTR [rsp+288]
	sub rsi, rdx
	sub rsi, 1
	mov rcx, rsi
	shr rcx, 3
	shl rcx, 3
	mov rax, QWORD PTR [rsp+264]
	mov r8d, 0
	test rcx, rcx
	je 223f
225:
	or rax, QWORD PTR [rdi+r8*1]
	add r8, 8
	cmp r8, rcx
	jne 225b
	jmp 224f
223:
224:
	cmp r8, rsi
	je 226f
228:
	movzx edx, BYTE PTR [rdi+r8*1]
	or rax, rdx
	add r8, 1
	cmp r8, rsi
	jne 228b
	jmp 227f
226:
227:
	movzx edx, BYTE PTR [rdi+rsi*1]
	xor rdx, 1
	or rax, rdx
	mov QWORD PTR [rsp+272], rsi
	mov QWORD PTR [rsp+264], rax
	mov rax, QWORD PTR [rsp+288]
	add rax, 36
	mov QWORD PTR [rsp+216], rax
219:
214:
	mov rax, QWORD PTR [rsp+280]
	test rax, rax
	je 229f
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov eax, 0
	mov r8d, 0
231:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 231b
	mov rsi, QWORD PTR [rsp+296]
	mov r8d, 0
232:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+8], al
	add r8, 1
	cmp r8, 28
	jne 232b
	mov rsi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
233:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+36], al
	add r8, 1
	cmp r8, r10
	jne 233b
	mov rax, QWORD PTR [rsp+272]
	add rax, 1
	mov QWORD PTR [rsp+360], rax
	mov eax, 1
	mov QWORD PTR [rsp+368], rax
	mov eax, 10
	mov QWORD PTR [rsp+352], rax
234:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3620
	mov rsi, QWORD PTR [rsp+368]
	add rsi, rcx
	mov r11, QWORD PTR [rsp+360]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
235:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 235b
	mov rax, QWORD PTR [rsp+360]
	shr rax, 1
	mov QWORD PTR [rsp+360], rax
	mov rax, QWORD PTR [rsp+368]
	add rax, rax
	mov QWORD PTR [rsp+368], rax
	mov rax, QWORD PTR [rsp+352]
	sub rax, 1
	mov QWORD PTR [rsp+352], rax
	jne 234b
	mov rax, QWORD PTR [rsp+192]
	add rax, 43
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
236:
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
	jne 236b
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
237:
	mov r11, r8
	xor r11, rdx
	cmp r11, 1
	sbb r11, r11
	mov r9d, 0
238:
	movzx eax, BYTE PTR [rsi+r9*1]
	and rax, r11
	movzx edi, BYTE PTR [rcx+r9*1]
	or rdi, rax
	mov BYTE PTR [rcx+r9*1], dil
	add r9, 1
	cmp r9, 8
	jne 238b
	add rcx, 64
	add r8, 1
	cmp r8, r10
	jne 237b
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
239:
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rcx, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+232]
	ror rsi, 58
	add rsi, rcx
	add rsi, 3584
	mov edx, 1
	call {vg_sha256_compress_shani}
	mov rcx, QWORD PTR [rsp+168]
	mov rax, QWORD PTR [rsp+232]
	xor rax, QWORD PTR [rsp+240]
	cmp rax, 1
	sbb r11, r11
	mov r8d, 0
240:
	movzx eax, BYTE PTR [rcx+r8*1+2048]
	movzx edx, BYTE PTR [rcx+r8*1+2240]
	xor rax, rdx
	and rax, r11
	xor rdx, rax
	mov BYTE PTR [rcx+r8*1+2240], dl
	add r8, 1
	cmp r8, 32
	jne 240b
	mov rax, QWORD PTR [rsp+232]
	add rax, 1
	mov QWORD PTR [rsp+232], rax
	mov rdx, QWORD PTR [rsp+224]
	cmp rax, rdx
	jne 239b
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
	add rcx, 2304
	mov rdi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+192]
	add rdi, rdx
	mov rdx, QWORD PTR [rsp+264]
	mov r8d, 0
241:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 28
	jne 241b
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
	jmp 230f
229:
	mov rax, QWORD PTR [rsp+288]
	cmp rax, QWORD PTR [rsp+192]
	jb 242f
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov eax, 0
	mov r8d, 0
244:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 244b
	mov rsi, QWORD PTR [rsp+296]
	mov r8d, 0
245:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+8], al
	add r8, 1
	cmp r8, 28
	jne 245b
	mov rsi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
246:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+36], al
	add r8, 1
	cmp r8, r10
	jne 246b
	mov rax, QWORD PTR [rsp+272]
	add rax, 1
	mov QWORD PTR [rsp+360], rax
	mov eax, 1
	mov QWORD PTR [rsp+368], rax
	mov eax, 10
	mov QWORD PTR [rsp+352], rax
247:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3620
	mov rsi, QWORD PTR [rsp+368]
	add rsi, rcx
	mov r11, QWORD PTR [rsp+360]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
248:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 248b
	mov rax, QWORD PTR [rsp+360]
	shr rax, 1
	mov QWORD PTR [rsp+360], rax
	mov rax, QWORD PTR [rsp+368]
	add rax, rax
	mov QWORD PTR [rsp+368], rax
	mov rax, QWORD PTR [rsp+352]
	sub rax, 1
	mov QWORD PTR [rsp+352], rax
	jne 247b
	mov rax, QWORD PTR [rsp+192]
	add rax, 43
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
249:
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
	jne 249b
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
250:
	mov r11, r8
	xor r11, rdx
	cmp r11, 1
	sbb r11, r11
	mov r9d, 0
251:
	movzx eax, BYTE PTR [rsi+r9*1]
	and rax, r11
	movzx edi, BYTE PTR [rcx+r9*1]
	or rdi, rax
	mov BYTE PTR [rcx+r9*1], dil
	add r9, 1
	cmp r9, 8
	jne 251b
	add rcx, 64
	add r8, 1
	cmp r8, r10
	jne 250b
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
252:
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rcx, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+232]
	ror rsi, 58
	add rsi, rcx
	add rsi, 3584
	mov edx, 1
	call {vg_sha256_compress_shani}
	mov rcx, QWORD PTR [rsp+168]
	mov rax, QWORD PTR [rsp+232]
	xor rax, QWORD PTR [rsp+240]
	cmp rax, 1
	sbb r11, r11
	mov r8d, 0
253:
	movzx eax, BYTE PTR [rcx+r8*1+2048]
	movzx edx, BYTE PTR [rcx+r8*1+2240]
	xor rax, rdx
	and rax, r11
	xor rdx, rax
	mov BYTE PTR [rcx+r8*1+2240], dl
	add r8, 1
	cmp r8, 32
	jne 253b
	mov rax, QWORD PTR [rsp+232]
	add rax, 1
	mov QWORD PTR [rsp+232], rax
	mov rdx, QWORD PTR [rsp+224]
	cmp rax, rdx
	jne 252b
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
	add rcx, 2304
	mov rdi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+192]
	add rdi, rdx
	mov rdx, QWORD PTR [rsp+264]
	mov r8d, 0
254:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 28
	jne 254b
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
	jmp 243f
242:
	mov rax, QWORD PTR [rsp+288]
	add rax, 36
	mov QWORD PTR [rsp+216], rax
	add rax, 8
	shr rax, 6
	add rax, 1
	mov QWORD PTR [rsp+224], rax
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov r10, QWORD PTR [rsp+224]
	ror r10, 58
	mov eax, 0
	mov r8d, 0
255:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, r10
	jne 255b
	mov rsi, QWORD PTR [rsp+296]
	mov r8d, 0
256:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+8], al
	add r8, 1
	cmp r8, 28
	jne 256b
	mov rsi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+192]
	add rsi, rax
	mov r10, QWORD PTR [rsp+288]
	sub rsi, r10
	mov r8d, 0
	test r10, r10
	je 257f
259:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+36], al
	add r8, 1
	cmp r8, r10
	jne 259b
	jmp 258f
257:
258:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov rdx, QWORD PTR [rsp+288]
	mov eax, 128
	mov BYTE PTR [rcx+rdx*1+36], al
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	call {vg_sha224_init}
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
	mov rax, QWORD PTR [rsp+224]
	ror rax, 58
	add rcx, rax
	add rcx, 3576
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rcx], rax
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
260:
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rcx, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+232]
	ror rsi, 58
	add rsi, rcx
	add rsi, 3584
	mov edx, 1
	call {vg_sha256_compress_shani}
	mov rax, QWORD PTR [rsp+232]
	add rax, 1
	mov QWORD PTR [rsp+232], rax
	mov rdx, QWORD PTR [rsp+224]
	cmp rax, rdx
	jne 260b
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
	mov rdi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+192]
	add rdi, rdx
	mov rdx, QWORD PTR [rsp+264]
	mov r8d, 0
261:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 28
	jne 261b
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
243:
230:
	jmp 26f
25:
	mov eax, 0
26:
	jmp 24f
23:
	mov eax, 0
24:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

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
