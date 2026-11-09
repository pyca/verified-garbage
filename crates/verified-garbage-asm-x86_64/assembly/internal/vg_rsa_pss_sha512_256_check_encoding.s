// The functions of `src/internal/vg_rsa_pss_sha512_256_check_encoding.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_sha512_256_check_encoding:
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
	mov r11, QWORD PTR [rsp+416]
	mov rax, QWORD PTR [r11]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [r11+24]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [r11+32]
	mov QWORD PTR [rsp+80], rax
	mov r11, QWORD PTR [rsp+424]
	mov rax, QWORD PTR [r11]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [r11+8]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [r11+16]
	mov QWORD PTR [rsp+104], rax
	mov rax, QWORD PTR [r11+32]
	mov QWORD PTR [rsp+112], rax
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
	cmp rax, 34
	jb 23f
	mov rax, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+208]
	sub rax, r8
	sub rax, 34
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
	mov rax, QWORD PTR [rsp+184]
	add rax, QWORD PTR [rsp+192]
	mov QWORD PTR [rsp+232], rax
	mov eax, 32
	mov QWORD PTR [rsp+240], rax
	mov eax, 0
	mov QWORD PTR [rsp+248], rax
	mov QWORD PTR [rsp+256], rax
27:
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov r11, QWORD PTR [rsp+88]
	call r11
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov esi, 0
	mov rdx, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rsp+240]
	mov r8, QWORD PTR [rsp+168]
	add r8, 0
	mov r11, QWORD PTR [rsp+96]
	call r11
	mov rdx, QWORD PTR [rsp+168]
	add rdx, 2368
	mov rax, QWORD PTR [rsp+248]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rsi, QWORD PTR [rsp+240]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+168]
	add r8, 0
	mov r11, QWORD PTR [rsp+96]
	call r11
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rsi, QWORD PTR [rsp+240]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+168]
	add rdx, 2304
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 0
	mov r11, QWORD PTR [rsp+104]
	call r11
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 2304
	mov rdx, QWORD PTR [rsp+256]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+192]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+112]
	cmp rax, r10
	jb 28f
	jmp 29f
28:
	mov r10, rax
29:
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 210b
	mov rax, QWORD PTR [rsp+248]
	add rax, 1
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+256]
	add rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp+256], rax
	cmp rax, QWORD PTR [rsp+192]
	jb 27b
	mov rdi, QWORD PTR [rsp+184]
	movzx eax, BYTE PTR [rdi]
	and rax, QWORD PTR [rsp+200]
	mov BYTE PTR [rdi], al
	mov rax, QWORD PTR [rsp+280]
	test rax, rax
	je 211f
	mov rdi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
	mov edx, 0
	mov esi, 0
	mov r11d, 0
213:
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
	jne 213b
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
	je 214f
	jmp 215f
214:
	mov r9, rcx
	xor r9, QWORD PTR [rsp+288]
	or rax, r9
215:
	mov QWORD PTR [rsp+264], rax
	add rcx, 40
	mov QWORD PTR [rsp+216], rcx
	jmp 212f
211:
	mov rax, QWORD PTR [rsp+288]
	cmp rax, QWORD PTR [rsp+192]
	jb 216f
	mov rdi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
	mov edx, 0
	mov esi, 0
	mov r11d, 0
218:
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
	jne 218b
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
	je 219f
	jmp 220f
219:
	mov r9, rcx
	xor r9, QWORD PTR [rsp+288]
	or rax, r9
220:
	mov QWORD PTR [rsp+264], rax
	add rcx, 40
	mov QWORD PTR [rsp+216], rcx
	jmp 217f
216:
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
	je 221f
223:
	or rax, QWORD PTR [rdi+r8*1]
	add r8, 8
	cmp r8, rcx
	jne 223b
	jmp 222f
221:
222:
	cmp r8, rsi
	je 224f
226:
	movzx edx, BYTE PTR [rdi+r8*1]
	or rax, rdx
	add r8, 1
	cmp r8, rsi
	jne 226b
	jmp 225f
224:
225:
	movzx edx, BYTE PTR [rdi+rsi*1]
	xor rdx, 1
	or rax, rdx
	mov QWORD PTR [rsp+272], rsi
	mov QWORD PTR [rsp+264], rax
	mov rax, QWORD PTR [rsp+288]
	add rax, 40
	mov QWORD PTR [rsp+216], rax
217:
212:
	mov rax, QWORD PTR [rsp+280]
	test rax, rax
	je 227f
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov eax, 0
	mov r8d, 0
229:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 229b
	mov rsi, QWORD PTR [rsp+296]
	mov r8d, 0
230:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+8], al
	add r8, 1
	cmp r8, 32
	jne 230b
	mov rsi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
231:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+40], al
	add r8, 1
	cmp r8, r10
	jne 231b
	mov rax, QWORD PTR [rsp+272]
	add rax, 1
	mov QWORD PTR [rsp+360], rax
	mov eax, 1
	mov QWORD PTR [rsp+368], rax
	mov eax, 10
	mov QWORD PTR [rsp+352], rax
232:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3624
	mov rsi, QWORD PTR [rsp+368]
	add rsi, rcx
	mov r11, QWORD PTR [rsp+360]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
233:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 233b
	mov rax, QWORD PTR [rsp+360]
	shr rax, 1
	mov QWORD PTR [rsp+360], rax
	mov rax, QWORD PTR [rsp+368]
	add rax, rax
	mov QWORD PTR [rsp+368], rax
	mov rax, QWORD PTR [rsp+352]
	sub rax, 1
	mov QWORD PTR [rsp+352], rax
	jne 232b
	mov rax, QWORD PTR [rsp+192]
	add rax, 55
	shr rax, 7
	add rax, 1
	mov QWORD PTR [rsp+224], rax
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov r11, QWORD PTR [rsp+64]
	call r11
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov rdx, QWORD PTR [rsp+216]
	mov r10, QWORD PTR [rsp+224]
	ror r10, 57
	mov r8d, 0
234:
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
	jne 234b
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
235:
	mov r11, r8
	xor r11, rdx
	cmp r11, 1
	sbb r11, r11
	mov r9d, 0
236:
	movzx eax, BYTE PTR [rsi+r9*1]
	and rax, r11
	movzx edi, BYTE PTR [rcx+r9*1]
	or rdi, rax
	mov BYTE PTR [rcx+r9*1], dil
	add r9, 1
	cmp r9, 16
	jne 236b
	add rcx, 128
	add r8, 1
	cmp r8, r10
	jne 235b
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
237:
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rcx, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+232]
	ror rsi, 57
	add rsi, rcx
	add rsi, 3584
	mov edx, 1
	mov r11, QWORD PTR [rsp+72]
	call r11
	mov rcx, QWORD PTR [rsp+168]
	mov rax, QWORD PTR [rsp+232]
	xor rax, QWORD PTR [rsp+240]
	cmp rax, 1
	sbb r11, r11
	mov r8d, 0
238:
	movzx eax, BYTE PTR [rcx+r8*1+2048]
	movzx edx, BYTE PTR [rcx+r8*1+2240]
	xor rax, rdx
	and rax, r11
	xor rdx, rax
	mov BYTE PTR [rcx+r8*1+2240], dl
	add r8, 1
	cmp r8, 64
	jne 238b
	mov rax, QWORD PTR [rsp+232]
	add rax, 1
	mov QWORD PTR [rsp+232], rax
	mov rdx, QWORD PTR [rsp+224]
	cmp rax, rdx
	jne 237b
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2240
	mov rsi, QWORD PTR [rsp+168]
	add rsi, 2304
	mov r11, QWORD PTR [rsp+80]
	call r11
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 2304
	mov rdi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+192]
	add rdi, rdx
	mov rdx, QWORD PTR [rsp+264]
	mov r8d, 0
239:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 239b
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
	jmp 228f
227:
	mov rax, QWORD PTR [rsp+288]
	cmp rax, QWORD PTR [rsp+192]
	jb 240f
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov eax, 0
	mov r8d, 0
242:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 242b
	mov rsi, QWORD PTR [rsp+296]
	mov r8d, 0
243:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+8], al
	add r8, 1
	cmp r8, 32
	jne 243b
	mov rsi, QWORD PTR [rsp+184]
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
244:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+40], al
	add r8, 1
	cmp r8, r10
	jne 244b
	mov rax, QWORD PTR [rsp+272]
	add rax, 1
	mov QWORD PTR [rsp+360], rax
	mov eax, 1
	mov QWORD PTR [rsp+368], rax
	mov eax, 10
	mov QWORD PTR [rsp+352], rax
245:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3624
	mov rsi, QWORD PTR [rsp+368]
	add rsi, rcx
	mov r11, QWORD PTR [rsp+360]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r10, QWORD PTR [rsp+192]
	mov r8d, 0
246:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 246b
	mov rax, QWORD PTR [rsp+360]
	shr rax, 1
	mov QWORD PTR [rsp+360], rax
	mov rax, QWORD PTR [rsp+368]
	add rax, rax
	mov QWORD PTR [rsp+368], rax
	mov rax, QWORD PTR [rsp+352]
	sub rax, 1
	mov QWORD PTR [rsp+352], rax
	jne 245b
	mov rax, QWORD PTR [rsp+192]
	add rax, 55
	shr rax, 7
	add rax, 1
	mov QWORD PTR [rsp+224], rax
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov r11, QWORD PTR [rsp+64]
	call r11
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov rdx, QWORD PTR [rsp+216]
	mov r10, QWORD PTR [rsp+224]
	ror r10, 57
	mov r8d, 0
247:
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
	jne 247b
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
248:
	mov r11, r8
	xor r11, rdx
	cmp r11, 1
	sbb r11, r11
	mov r9d, 0
249:
	movzx eax, BYTE PTR [rsi+r9*1]
	and rax, r11
	movzx edi, BYTE PTR [rcx+r9*1]
	or rdi, rax
	mov BYTE PTR [rcx+r9*1], dil
	add r9, 1
	cmp r9, 16
	jne 249b
	add rcx, 128
	add r8, 1
	cmp r8, r10
	jne 248b
	mov eax, 0
	mov QWORD PTR [rsp+232], rax
250:
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rcx, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+232]
	ror rsi, 57
	add rsi, rcx
	add rsi, 3584
	mov edx, 1
	mov r11, QWORD PTR [rsp+72]
	call r11
	mov rcx, QWORD PTR [rsp+168]
	mov rax, QWORD PTR [rsp+232]
	xor rax, QWORD PTR [rsp+240]
	cmp rax, 1
	sbb r11, r11
	mov r8d, 0
251:
	movzx eax, BYTE PTR [rcx+r8*1+2048]
	movzx edx, BYTE PTR [rcx+r8*1+2240]
	xor rax, rdx
	and rax, r11
	xor rdx, rax
	mov BYTE PTR [rcx+r8*1+2240], dl
	add r8, 1
	cmp r8, 64
	jne 251b
	mov rax, QWORD PTR [rsp+232]
	add rax, 1
	mov QWORD PTR [rsp+232], rax
	mov rdx, QWORD PTR [rsp+224]
	cmp rax, rdx
	jne 250b
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2240
	mov rsi, QWORD PTR [rsp+168]
	add rsi, 2304
	mov r11, QWORD PTR [rsp+80]
	call r11
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 2304
	mov rdi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+192]
	add rdi, rdx
	mov rdx, QWORD PTR [rsp+264]
	mov r8d, 0
252:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 252b
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
	jmp 241f
240:
	mov rax, QWORD PTR [rsp+288]
	add rax, 40
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
253:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, r10
	jne 253b
	mov rsi, QWORD PTR [rsp+296]
	mov r8d, 0
254:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+8], al
	add r8, 1
	cmp r8, 32
	jne 254b
	mov rsi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+192]
	add rsi, rax
	mov r10, QWORD PTR [rsp+288]
	sub rsi, r10
	mov r8d, 0
	test r10, r10
	je 255f
257:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+40], al
	add r8, 1
	cmp r8, r10
	jne 257b
	jmp 256f
255:
256:
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 3584
	mov rdx, QWORD PTR [rsp+288]
	mov eax, 128
	mov BYTE PTR [rcx+rdx*1+40], al
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov r11, QWORD PTR [rsp+64]
	call r11
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
258:
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rcx, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+232]
	ror rsi, 57
	add rsi, rcx
	add rsi, 3584
	mov edx, 1
	mov r11, QWORD PTR [rsp+72]
	call r11
	mov rax, QWORD PTR [rsp+232]
	add rax, 1
	mov QWORD PTR [rsp+232], rax
	mov rdx, QWORD PTR [rsp+224]
	cmp rax, rdx
	jne 258b
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2048
	mov rsi, QWORD PTR [rsp+168]
	add rsi, 2304
	mov r11, QWORD PTR [rsp+80]
	call r11
	mov rcx, QWORD PTR [rsp+168]
	add rcx, 2304
	mov rdi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+192]
	add rdi, rdx
	mov rdx, QWORD PTR [rsp+264]
	mov r8d, 0
259:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 259b
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
241:
228:
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
