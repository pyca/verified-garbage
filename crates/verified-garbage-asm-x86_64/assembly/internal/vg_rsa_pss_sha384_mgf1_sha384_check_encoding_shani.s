// The functions of `src/internal/vg_rsa_pss_sha384_mgf1_sha384_check_encoding_shani.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_sha384_mgf1_sha384_check_encoding_shani:
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
	cmp rax, 50
	jb 23f
	mov rax, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+208]
	sub rax, r8
	sub rax, 50
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
	cmp r8, 128
	jne 28b
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
	jb 29f
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
	jmp 210f
29:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 2304
	mov rdx, QWORD PTR [rsp+256]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+192]
	sub rax, rdx
	mov r10d, 48
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
210:
	mov rax, QWORD PTR [rsp+248]
	add rax, 1
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+256]
	add rax, 48
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
	je 214f
	mov rdi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
	mov edx, 0
	mov esi, 0
	mov r11d, 0
216:
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
	jne 216b
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
	je 217f
	jmp 218f
217:
	mov r9, rcx
	xor r9, QWORD PTR [rsp+288]
	or rax, r9
218:
	mov QWORD PTR [rsp+264], rax
	add rcx, 56
	mov QWORD PTR [rsp+216], rcx
	jmp 215f
214:
	mov rax, QWORD PTR [rsp+288]
	cmp rax, QWORD PTR [rsp+192]
	jb 219f
	mov rdi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
	mov edx, 0
	mov esi, 0
	mov r11d, 0
221:
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
	jne 221b
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
	je 222f
	jmp 223f
222:
	mov r9, rcx
	xor r9, QWORD PTR [rsp+288]
	or rax, r9
223:
	mov QWORD PTR [rsp+264], rax
	add rcx, 56
	mov QWORD PTR [rsp+216], rcx
	jmp 220f
219:
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
	je 224f
226:
	or rax, QWORD PTR [rdi+r8*1]
	add r8, 8
	cmp r8, rcx
	jne 226b
	jmp 225f
224:
225:
	cmp r8, rsi
	je 227f
229:
	movzx edx, BYTE PTR [rdi+r8*1]
	or rax, rdx
	add r8, 1
	cmp r8, rsi
	jne 229b
	jmp 228f
227:
228:
	movzx edx, BYTE PTR [rdi+rsi*1]
	xor rdx, 1
	or rax, rdx
	mov QWORD PTR [rsp+272], rsi
	mov QWORD PTR [rsp+264], rax
	mov rax, QWORD PTR [rsp+288]
	add rax, 56
	mov QWORD PTR [rsp+216], rax
220:
215:
	mov rax, QWORD PTR [rsp+280]
	test rax, rax
	je 230f
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov eax, 0
	mov r8d, 0
232:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 232b
	mov rsi, QWORD PTR [rsp+296]
	mov r8d, 0
233:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+8], al
	add r8, 1
	cmp r8, 48
	jne 233b
	mov rsi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
234:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+56], al
	add r8, 1
	cmp r8, r10
	jne 234b
	mov rax, QWORD PTR [rsp+272]
	add rax, 1
	mov QWORD PTR [rsp+360], rax
	mov eax, 1
	mov QWORD PTR [rsp+368], rax
	mov eax, 10
	mov QWORD PTR [rsp+352], rax
235:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3640
	mov rsi, QWORD PTR [rsp+368]
	add rsi, rcx
	mov r11, QWORD PTR [rsp+360]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
236:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 236b
	mov rax, QWORD PTR [rsp+360]
	shr rax, 1
	mov QWORD PTR [rsp+360], rax
	mov rax, QWORD PTR [rsp+368]
	add rax, rax
	mov QWORD PTR [rsp+368], rax
	mov rax, QWORD PTR [rsp+352]
	sub rax, 1
	mov QWORD PTR [rsp+352], rax
	jne 235b
	mov rax, QWORD PTR [rsp+192]
	add rax, 71
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
237:
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
	jne 237b
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
238:
	mov r11, r8
	xor r11, rdx
	cmp r11, 1
	sbb r11, r11
	mov r9d, 0
239:
	movzx eax, BYTE PTR [rsi+r9*1]
	and rax, r11
	movzx edi, BYTE PTR [rcx+r9*1]
	or rdi, rax
	mov BYTE PTR [rcx+r9*1], dil
	add r9, 1
	cmp r9, 16
	jne 239b
	add rcx, 128
	add r8, 1
	cmp r8, r10
	jne 238b
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
240:
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
241:
	movzx eax, BYTE PTR [rcx+r8*1+2048]
	movzx edx, BYTE PTR [rcx+r8*1+2240]
	xor rax, rdx
	and rax, r11
	xor rdx, rax
	mov BYTE PTR [rcx+r8*1+2240], dl
	add r8, 1
	cmp r8, 64
	jne 241b
	mov rax, QWORD PTR [rsp+232]
	add rax, 1
	mov QWORD PTR [rsp+232], rax
	mov rdx, QWORD PTR [rsp+224]
	cmp rax, rdx
	jne 240b
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
	add rcx, 2304
	mov rdi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+192]
	add rdi, rdx
	mov rdx, QWORD PTR [rsp+264]
	mov r8d, 0
242:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 48
	jne 242b
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
	jmp 231f
230:
	mov rax, QWORD PTR [rsp+288]
	cmp rax, QWORD PTR [rsp+192]
	jb 243f
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov eax, 0
	mov r8d, 0
245:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 245b
	mov rsi, QWORD PTR [rsp+296]
	mov r8d, 0
246:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+8], al
	add r8, 1
	cmp r8, 48
	jne 246b
	mov rsi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
247:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+56], al
	add r8, 1
	cmp r8, r10
	jne 247b
	mov rax, QWORD PTR [rsp+272]
	add rax, 1
	mov QWORD PTR [rsp+360], rax
	mov eax, 1
	mov QWORD PTR [rsp+368], rax
	mov eax, 10
	mov QWORD PTR [rsp+352], rax
248:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3640
	mov rsi, QWORD PTR [rsp+368]
	add rsi, rcx
	mov r11, QWORD PTR [rsp+360]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
249:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 249b
	mov rax, QWORD PTR [rsp+360]
	shr rax, 1
	mov QWORD PTR [rsp+360], rax
	mov rax, QWORD PTR [rsp+368]
	add rax, rax
	mov QWORD PTR [rsp+368], rax
	mov rax, QWORD PTR [rsp+352]
	sub rax, 1
	mov QWORD PTR [rsp+352], rax
	jne 248b
	mov rax, QWORD PTR [rsp+192]
	add rax, 71
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
250:
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
	jne 250b
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
251:
	mov r11, r8
	xor r11, rdx
	cmp r11, 1
	sbb r11, r11
	mov r9d, 0
252:
	movzx eax, BYTE PTR [rsi+r9*1]
	and rax, r11
	movzx edi, BYTE PTR [rcx+r9*1]
	or rdi, rax
	mov BYTE PTR [rcx+r9*1], dil
	add r9, 1
	cmp r9, 16
	jne 252b
	add rcx, 128
	add r8, 1
	cmp r8, r10
	jne 251b
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
253:
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
254:
	movzx eax, BYTE PTR [rcx+r8*1+2048]
	movzx edx, BYTE PTR [rcx+r8*1+2240]
	xor rax, rdx
	and rax, r11
	xor rdx, rax
	mov BYTE PTR [rcx+r8*1+2240], dl
	add r8, 1
	cmp r8, 64
	jne 254b
	mov rax, QWORD PTR [rsp+232]
	add rax, 1
	mov QWORD PTR [rsp+232], rax
	mov rdx, QWORD PTR [rsp+224]
	cmp rax, rdx
	jne 253b
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
	add rcx, 2304
	mov rdi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+192]
	add rdi, rdx
	mov rdx, QWORD PTR [rsp+264]
	mov r8d, 0
255:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 48
	jne 255b
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
	jmp 244f
243:
	mov rax, QWORD PTR [rsp+288]
	add rax, 56
	mov QWORD PTR [rsp+216], rax
	add rax, 16
	shr rax, 7
	add rax, 1
	mov QWORD PTR [rsp+224], rax
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov r10, QWORD PTR [rsp+224]
	ror r10, 57
	mov eax, 0
	mov r8d, 0
256:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, r10
	jne 256b
	mov rsi, QWORD PTR [rsp+296]
	mov r8d, 0
257:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+8], al
	add r8, 1
	cmp r8, 48
	jne 257b
	mov rsi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+192]
	add rsi, rax
	mov r10, QWORD PTR [rsp+288]
	sub rsi, r10
	mov r8d, 0
	test r10, r10
	je 258f
260:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+56], al
	add r8, 1
	cmp r8, r10
	jne 260b
	jmp 259f
258:
259:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov rdx, QWORD PTR [rsp+288]
	mov eax, 128
	mov BYTE PTR [rcx+rdx*1+56], al
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	call {vg_sha384_init}
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
	mov rax, QWORD PTR [rsp+224]
	ror rax, 57
	add rcx, rax
	add rcx, 3568
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rcx+8], rax
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
261:
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rcx, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+232]
	ror rsi, 57
	add rsi, rcx
	add rsi, 3584
	mov edx, 1
	call {vg_sha512_compress_shani}
	mov rax, QWORD PTR [rsp+232]
	add rax, 1
	mov QWORD PTR [rsp+232], rax
	mov rdx, QWORD PTR [rsp+224]
	cmp rax, rdx
	jne 261b
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
	mov rdi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+192]
	add rdi, rdx
	mov rdx, QWORD PTR [rsp+264]
	mov r8d, 0
262:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 48
	jne 262b
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
244:
231:
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
